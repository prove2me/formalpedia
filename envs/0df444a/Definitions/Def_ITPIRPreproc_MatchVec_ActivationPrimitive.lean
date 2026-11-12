-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive
-- name    : ITPIRPreproc_MatchVec_ActivationPrimitive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:16.520925+00:00
-- url     : https://prove2.me/theorems/dcbfc2ec-f5e3-40eb-9c23-a14be73d2d2b
-- title:
--   §6.2 — the matching-vector One Compatible Hint PIR with activation bits, (14)–(17)
-- statement:
--   Let $m=2^h$, let $u_a,v_a\in\mathbb Z_6^d$ ($a\in[m]$) be matching vectors, and let $D\in\{0,1\}^{m\times m}$ with columns $b\in\mathbb F_2^h$ identified with $[m]$ by binary expansion. Column and activation products are over $\mathbb F_2$ (vectors reduced mod 2); weighted sums and decoding are over $\mathbb F_3$ (vectors reduced mod 3, bits embedded as $0,1$).
--
--   * **Keys** $(R,\rho)\in\mathcal R^+=\mathbb F_2^{h\times d}\times\mathbb F_2^d$; row $a$ is *active* when $\langle\rho,v_a\rangle_2=1$, and
--   $$S(R,\rho)=\{(a,Rv_a): a\in[m],\ \langle\rho,v_a\rangle_2=1\}. \tag{14}$$
--   * **Sampler** for $\mathcal R^+_i$, $i=(a^\star,b^\star)$: $(R_0,\rho_0)\mapsto\big(R_0+(b^\star-R_0v_{a^\star})u_{a^\star}^T,\ \rho_0+(1-\langle\rho_0,v_{a^\star}\rangle_2)u_{a^\star}\big)$. (15)
--   * $\mathsf{Hint}(D,(R,\rho))=\sum_{a:\langle\rho,v_a\rangle_2=1}D[a,Rv_a]\,v_a\in\mathbb F_3^d$.
--   * $\mathsf{Query}(i,(R,\rho))$: uniform independent $\gamma\in\mathbb F_2$, $\delta\in\mathbb F_2^h$; query $(Q,\tilde\rho)=(R+\delta u_{a^\star}^T,\ \rho+\gamma u_{a^\star})$, private state $u=\gamma$. (16)
--   * $\mathsf{Answer}(D,(Q,\tilde\rho))=\mathsf{Hint}(D,(Q,\tilde\rho))$.
--   * $\mathsf{Decode}(i,(R,\rho),z,Q,u,z')=\bot$ if $u=0$, and $\langle u_{a^\star},z-z'\rangle_3$ otherwise. (17)
--
--   For the generic interface of Definition 4.1 the positions of $[m]\times[m]$ are numbered row-major, a decoded value $0$ or $1$ of $\mathbb F_3$ is that bit and the value $2$ is reported as $\bot$; the family indexed by $m$ uses, at $m=2^h$, the matching vectors of index $h$ (and a placeholder primitive when $m$ is not a power of two).
--
--   This is the primitive of Lemma 6.2, which the compiler of Lemma 4.2 turns into the scheme of Theorem 6.1.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), §6.2, printed pp.20–21 (PDF pp.22–23), Eq. (14)–(17)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_BasicKeys
import Definitions.Def_ITPIRPreproc_MatchVec_OneCompatibleHint

open scoped ENNReal
open Matrix

namespace ITPIRPreproc.MatchVec

/-!
# The matching-vector primitive with activation bits (§6.2, printed pp.20–21)

"Use the padded matrix layout and matching vectors of Section 5.2, so n = m² and h = log₂ m.
Column and activation products are over F₂; weighted sums and decoding are over F₃."

"Keys and selected sets. The key space is R⁺ = F₂^{h×d} × F₂^d. For a key (R, ρ), row a is active
when ⟨ρ, v_a⟩₂ = 1. Define S(R, ρ) = {(a, Rv_a) : a ∈ [m], ⟨ρ, v_a⟩₂ = 1}. (14)"

"To sample from R⁺_i, sample independent uniform R₀ ∈ F₂^{h×d} and ρ₀ ∈ F₂^d, and return
R = R₀ + (b⋆ − R₀v_{a⋆})u_{a⋆}^T, ρ = ρ₀ + (1 − ⟨ρ₀, v_{a⋆}⟩₂)u_{a⋆}. (15)"

"1. Hint(D, (R, ρ)) returns z = Σ_{a : ⟨ρ,v_a⟩₂=1} D[a, Rv_a] v_a ∈ F₃^d.
2. Query(i, (R, ρ)), for a compatible key, samples independent γ ← F₂ and δ ← F₂^h. Set
Q = R + δu_{a⋆}^T, ρ̃ = ρ + γu_{a⋆}. (16) Return (Q, u) with query Q = (Q, ρ̃) and secret state
u = γ.
3. Answer(D, Q) returns z′ = Hint(D, (Q, ρ̃)).
4. Decode(i, (R, ρ), z, Q, u, z′) returns ⊥ if u = 0. Otherwise return ⟨u_{a⋆}, z − z′⟩₃. (17)"

The database is `D : Fin m → Fin m → Bool` (`m = 2^h`), `D[a, b] = D a (colIdx b)`, and a bit is
embedded in `F₃` as `0, 1` (`bitF3`). The decoder returns `Option (ZMod 3)` (`none` is `⊥`).
For the generic interface of Definition 4.1 (`OCHP`), positions `Fin (m·m)` are read in row-major
order (`finProdFinEquiv`: index `c + m·a` is row `a`, column `c`), and a decoded value `0`/`1` of
`F₃` is the bit `0`/`1` while `2` is reported as `⊥`.
-/

variable {h d : ℕ}

/-- The key space `R⁺ = F₂^{h×d} × F₂^d`. -/
abbrev ActKey (h d : ℕ) := BasicKey h d × (Fin d → ZMod 2)

/-- A database `D ∈ {0,1}^{m×m}`, `m = 2^h`. -/
abbrev DB (h : ℕ) := Fin (2 ^ h) → Fin (2 ^ h) → Bool

/-- The bit `0`/`1` as an element of `F₃`. -/
def bitF3 (b : Bool) : ZMod 3 :=
  if b then 1 else 0

/-- `(a, b) ∈ S(R, ρ)` (14): `R v_a = b` and row `a` is active, `⟨ρ, v_a⟩₂ = 1`. -/
def actSel (v : Fin (2 ^ h) → Fin d → ZMod 6) (K : ActKey h d) (i : Pos h) : Prop :=
  K.1 *ᵥ vec2 (v i.1) = i.2 ∧ K.2 ⬝ᵥ vec2 (v i.1) = 1

instance (v : Fin (2 ^ h) → Fin d → ZMod 6) (K : ActKey h d) (i : Pos h) :
    Decidable (actSel v K i) := by
  unfold actSel; infer_instance

/-- The compatible keys `R⁺_i`. -/
def actCompat (v : Fin (2 ^ h) → Fin d → ZMod 6) (i : Pos h) : Finset (ActKey h d) :=
  Finset.univ.filter fun K => actSel v K i

/-- The conditional sampler (15). -/
def actSampler (u v : Fin (2 ^ h) → Fin d → ZMod 6) (i : Pos h) (K₀ : ActKey h d) :
    ActKey h d :=
  (K₀.1 + Matrix.vecMulVec (i.2 - K₀.1 *ᵥ vec2 (v i.1)) (vec2 (u i.1)),
   K₀.2 + (1 - K₀.2 ⬝ᵥ vec2 (v i.1)) • vec2 (u i.1))

/-- `Hint(D, (R, ρ)) = Σ_{a : ⟨ρ, v_a⟩₂ = 1} D[a, R v_a] v_a ∈ F₃^d`. -/
def actHint (v : Fin (2 ^ h) → Fin d → ZMod 6) (D : DB h) (K : ActKey h d) : Fin d → ZMod 3 :=
  ∑ a : Fin (2 ^ h),
    if K.2 ⬝ᵥ vec2 (v a) = 1 then bitF3 (D a (colIdx (K.1 *ᵥ vec2 (v a)))) • vec3 (v a) else 0

/-- The query map (16) on coins `(γ, δ) ∈ F₂ × F₂^h`: `(R + δ u_{a⋆}^T, ρ + γ u_{a⋆})`. -/
def actQueryMap (u : Fin (2 ^ h) → Fin d → ZMod 6) (i : Pos h) (K : ActKey h d)
    (c : ZMod 2 × (Fin h → ZMod 2)) : ActKey h d :=
  (K.1 + Matrix.vecMulVec c.2 (vec2 (u i.1)), K.2 + c.1 • vec2 (u i.1))

/-- `Query(i, (R, ρ))`: uniform `(γ, δ)`, query `(Q, ρ̃)` of (16), secret `u = γ`. -/
noncomputable def actQuery (u : Fin (2 ^ h) → Fin d → ZMod 6) (i : Pos h) (K : ActKey h d) :
    PMF (ActKey h d × ZMod 2) :=
  (PMF.uniformOfFintype (ZMod 2 × (Fin h → ZMod 2))).map fun c => (actQueryMap u i K c, c.1)

/-- `Answer(D, Q) = Hint(D, (Q, ρ̃))`. -/
def actAnswer (v : Fin (2 ^ h) → Fin d → ZMod 6) (D : DB h) (Q : ActKey h d) : Fin d → ZMod 3 :=
  actHint v D Q

/-- `Decode(i, (R, ρ), z, Q, u, z′)` (17): `⊥` if `u = 0`, otherwise `⟨u_{a⋆}, z − z′⟩₃`. -/
def actDecode (u : Fin (2 ^ h) → Fin d → ZMod 6) (i : Pos h) (_K : ActKey h d)
    (z : Fin d → ZMod 3) (_Q : ActKey h d) (γ : ZMod 2) (z' : Fin d → ZMod 3) :
    Option (ZMod 3) :=
  if γ = 0 then none else some (vec3 (u i.1) ⬝ᵥ (z - z'))

/-- The position `(a, b)` of the row-major index `i ∈ Fin (m·m)`. -/
def posOf (i : Fin (2 ^ h * 2 ^ h)) : Pos h :=
  ((finProdFinEquiv.symm i).1, colVec (finProdFinEquiv.symm i).2)

/-- The matrix form of a database given as a row-major bit vector of length `m·m`. -/
def toDB (D : Fin (2 ^ h * 2 ^ h) → Bool) : DB h :=
  fun a c => D (finProdFinEquiv (a, c))

/-- A decoded `F₃` value read as a bit (`2` and `⊥` give `⊥`). -/
def toBitOpt : Option (ZMod 3) → Option Bool
  | some x => if x = 0 then some false else if x = 1 then some true else none
  | none => none

/-- The §6.2 primitive as a One Compatible Hint PIR for databases of length `m² = 4^h`. -/
noncomputable def actPrimitive (d : ℕ) (u v : Fin (2 ^ h) → Fin d → ZMod 6) :
    OCHP (2 ^ h * 2 ^ h) where
  Key := ActKey h d
  sel K := Finset.univ.filter fun i => actSel v K (posOf i)
  HintVal := Fin d → ZMod 3
  Secret := ZMod 2
  AnsVal := Fin d → ZMod 3
  hint D K := actHint v (toDB D) K
  query i K := actQuery u (posOf i) K
  answer D Q := actAnswer v (toDB D) Q
  decode i K z Q γ z' := toBitOpt (actDecode u (posOf i) K z Q γ z')

/-- A placeholder primitive (one key, empty selected set) for sizes that are not powers of
two. -/
noncomputable def trivialOCHP (n : ℕ) : OCHP n where
  Key := Unit
  sel _ := ∅
  HintVal := Unit
  Secret := Unit
  AnsVal := Unit
  hint _ _ := ()
  query _ _ := PMF.pure ((), ())
  answer _ _ := ()
  decode _ _ _ _ _ _ := none

/-- The family `m ↦` the §6.2 primitive at `m = 2^h` built from the matching-vector family
`(u h, v h)` of dimension `dim h`; for `m` not a power of two, the placeholder. -/
noncomputable def actFamily (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6) :
    ∀ m : ℕ, OCHP (m * m) :=
  fun m =>
    if hm : 2 ^ Nat.log 2 m = m then
      cast (congrArg (fun t => OCHP (t * t)) hm)
        (actPrimitive (dim (Nat.log 2 m)) (u (Nat.log 2 m)) (v (Nat.log 2 m)))
    else trivialOCHP (m * m)

end ITPIRPreproc.MatchVec


