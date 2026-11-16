-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_Supplement_Majority
-- name    : ITPIRPreproc_MatchVec_Supplement_Majority
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:50:08.564178+00:00
-- url     : https://prove2.me/theorems/30e152b9-1284-43c1-b0a5-8ba9f864179a
-- title:
--   The majority construction of One Compatible Hint PIR (§7.2–§7.3)
-- statement:
--   This file defines the objects of the majority construction of Dujmovic, Lai and Wichs (§7.2–§7.3).
--
--   **Layout and parameters.** Let $m=2^h$. Database rows are $a\in[m]$, each identified with its binary label in $\mathbb F_2^h$, and columns are labelled by sign vectors $b\in\{-1,+1\}^h$, so a database is $D\in\{0,1\}^{m\times m}$ with entries $D[a,b]$ and a position is a pair $(a,b)$. For an integer construction parameter $H$ set
--   $$d=2H^{14}+1,\qquad \Delta=H^5,\qquad \mu=H^{-6}.$$
--   The label length is $H^2+\lceil 4\log_2 d\rceil$. For sign vectors, $\langle x,y\rangle=\sum_k x_ky_k$ is the integer inner product.
--
--   **Seeds.** A seed is $\sigma=((g_k,\tau_k))_{k\in[d]}$ with $(g_k,\tau_k)\in\mathbb F_2^h\times\mathbb F_2$. It determines the row vectors $v_a\in\{-1,+1\}^d$, $v_{a,k}=(-1)^{\langle a,g_k\rangle_2+\tau_k}$. The seed is **good** when $|\langle v_a,v_{a'}\rangle|\le\mu d$ for all $a\ne a'$.
--
--   **Keys.** The key space is $\mathcal R=\{-1,+1\}^{h\times d}$. The $h$ rows $r_t$ of a key are its blocks. The selected set is $S(R)=\{(a,\operatorname{sgn}(Rv_a)):a\in[m]\}$. Since $d$ is odd there are no ties. The compatible keys are $\mathcal R_i=\{R:i\in S(R)\}$. The conditional sampler for $i=(a^\star,b^\star)$ replaces each block $r_t$ by $-r_t$ whenever $\operatorname{sgn}\langle r_t,v_{a^\star}\rangle\ne b^\star_t$.
--
--   **Query.** $\mathrm{Query}(i,R)$ draws independent uniform coins:
--
--   1. a retain/flip coin for every block;
--   2. a label of $H^2+\lceil4\log_2 d\rceil$ bits for every coordinate of every block;
--   3. a fresh uniform key.
--
--   If two labels collide within a block, the query returns the fresh key with $u=\mathrm{fail}$. Otherwise every retained block is kept. In every flipped block $t$, put $F_t=b^\star_t\langle r_t,v_{a^\star}\rangle$; among the coordinates $k$ with $r_{t,k}=b^\star_tv_{a^\star,k}$, the $F_t$ with the smallest labels are negated, and the query returns $u=\mathrm{ok}$.
--
--   **Answer.** The reported positions are
--   $$S^+(Q)=\{(a,b):b_t\langle q_t,v_a\rangle\ge-\Delta\ \text{for all }t\}.$$
--   $\mathrm{Answer}(D,Q)$ enumerates $S^+(Q)$ in row order, and within a row in lexicographic order of the column labels. It aborts if there are more than $8m$ reported positions, and otherwise returns the list $\beta$ of the bits $D[a,b]$ in that order.
--
--   **Hint and Decode.** $\mathrm{Hint}(D,R)=\bigoplus_a D[a,\operatorname{sgn}(Rv_a)]$. $\mathrm{Decode}(i,R,z,Q,u,\mathrm{ans})$ returns $\bot$ in three cases: $u=\mathrm{fail}$, the answer aborts, or some position of $S(R)\setminus\{i\}$ is not reported. Otherwise it returns $z\oplus\bigoplus_{(a,b)\in S(R)\setminus\{i\}}\beta_{a,b}$.
--
--   These objects are the majority primitive whose properties are Claims 7.4.1–7.4.3 and which the full scheme of Theorem 7.1 runs with a random seed.
--
--   **Formalization Note** Signs are the units $\mathbb Z^\times=\{\pm1\}$. Row labels use the published binary-digit map `colVec`. $\lceil4\log_2 d\rceil$ is `Nat.clog 2 (d^4)`. The lexicographic order puts coordinate $0$ first and $-1$ before $+1$. `Query` is a probability mass function on (key, $u$), with $u=\mathrm{ok}$ written `true`. Its fresh key is drawn with the other coins and used only on a collision, which gives the same output law. When labels are distinct, "the $F_t$ eligible coordinates with the smallest labels" are the eligible coordinates with fewer than $F_t$ eligible coordinates of smaller label. Decode looks up each position of $S(R)\setminus\{i\}$ in the pairing of the enumeration of $S^+(Q)$ with $\beta$.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), §7.2 Eq. (19)–(21), printed pp.24–26 (PDF pp.26–28); §7.3 Eq. (22)–(24) and Retrieval algorithms, printed pp.26–27 (PDF pp.28–29)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_BasicKeys
import Definitions.Def_ITPIRPreproc_MatchVec_OneCompatibleHint

open scoped ENNReal
open Matrix

namespace ITPIRPreproc.MatchVec.Supplement

/-!
# The majority construction of One Compatible Hint PIR (§7.2–§7.3, printed pp.24–27)

"We use the padded matrix layout of Section 5.2, so n = m² and h = log₂ m, except that columns
are now labeled by sign vectors b ∈ {−1,+1}^h. All matrix products in this section are over the
integers, and sgn acts coordinatewise. Fix an integer construction parameter H ≥ h + 64, and set
d = 2H^14 + 1, ∆ = H^5, µ = H^{−6}. (19)"

Conventions.
* `m = 2^h`; rows are `a ∈ Fin (2^h)`, identified with their binary label `colVec a ∈ F₂^h`
  (published in `Def_ITPIRPreproc_MatchVec_BasicKeys`: digit `t` is bit `t` of `a`).
* Signs are units of `ℤ` (`ℤˣ = {−1, +1}`); a sign vector of length `k` is `Fin k → ℤˣ`, and
  `⟨x, y⟩ = Σ_k x_k y_k ∈ ℤ`.
* A position is `(a, b) ∈ [m] × {−1,+1}^h` (`MPos h`); a database is `D : [m] → {−1,+1}^h → Bool`
  (`D[a, b]`, columns labelled by sign vectors).
* Probabilities are uniform laws on finite sets, written with cardinalities or with `avgOver`
  (published in `Def_ITPIRPreproc_MatchVec_OneCompatibleHint`); the randomized `Query` is a `PMF`.
-/

/-- The dimension `d = 2H^14 + 1` of (19). -/
def dim (H : ℕ) : ℕ := 2 * H ^ 14 + 1

/-- The shift `∆ = H^5` of (19). -/
def shift (H : ℕ) : ℤ := (H : ℤ) ^ 5

/-- The near-orthogonality parameter `µ = H^{−6}` of (19). -/
noncomputable def mu (H : ℕ) : ℝ := ((H : ℝ) ^ 6)⁻¹

/-- The label length `H² + ⌈4 log₂ d⌉` of Query step (a); `⌈4 log₂ d⌉ = ⌈log₂ d⁴⌉ = Nat.clog 2 (d⁴)`. -/
def labelBits (H : ℕ) : ℕ := H ^ 2 + Nat.clog 2 (dim H ^ 4)

/-- The integer inner product `⟨x, y⟩ = Σ_k x_k y_k` of two sign vectors. -/
def ip {k : ℕ} (x y : Fin k → ℤˣ) : ℤ := ∑ j, (x j : ℤ) * (y j : ℤ)

/-- A seed `σ = ((g_k, τ_k))_{k ∈ [d]}` with `(g_k, τ_k) ∈ F₂^h × F₂`. -/
abbrev Seed (h H : ℕ) := Fin (dim H) → (Fin h → ZMod 2) × ZMod 2

/-- The row vector (20): `v_{a,k} = (−1)^{⟨a, g_k⟩₂ + τ_k}`, `a` read as its binary label. -/
def rowVec {h H : ℕ} (σ : Seed h H) (a : Fin (2 ^ h)) : Fin (dim H) → ℤˣ :=
  fun k => if colVec a ⬝ᵥ (σ k).1 + (σ k).2 = 0 then 1 else -1

/-- The seed is **good** (21): `|⟨v_a, v_{a′}⟩| ≤ µ d` for all rows `a ≠ a′`. -/
def IsGood {h H : ℕ} (σ : Seed h H) : Prop :=
  ∀ a a' : Fin (2 ^ h), a ≠ a' →
    |((ip (rowVec σ a) (rowVec σ a') : ℤ) : ℝ)| ≤ mu H * (dim H : ℝ)

noncomputable instance {h H : ℕ} (σ : Seed h H) : Decidable (IsGood σ) := by
  unfold IsGood; infer_instance

/-- The key space `R = {−1,+1}^{h×d}`; `R t` is block `t` (the row `r_t^T`). -/
abbrev Key (h H : ℕ) := Fin h → Fin (dim H) → ℤˣ

/-- A position `(a, b) ∈ [m] × {−1,+1}^h`. -/
abbrev MPos (h : ℕ) := Fin (2 ^ h) × (Fin h → ℤˣ)

/-- A database `D ∈ {0,1}^{m×m}`, columns labelled by sign vectors. -/
abbrev MDB (h : ℕ) := Fin (2 ^ h) → (Fin h → ℤˣ) → Bool

/-- The column `sgn(R v_a) ∈ {−1,+1}^h` selected by key `R` in row `a` (`d` is odd, so
`⟨r_t, v_a⟩ ≠ 0` and the sign is `+1` exactly when the inner product is positive). -/
def selCol {h H : ℕ} (σ : Seed h H) (R : Key h H) (a : Fin (2 ^ h)) : Fin h → ℤˣ :=
  fun t => if 0 < ip (R t) (rowVec σ a) then 1 else -1

/-- `i ∈ S(R)` for the selected set (22) `S(R) = {(a, sgn(R v_a)) : a ∈ [m]}`. -/
def majSel {h H : ℕ} (σ : Seed h H) (R : Key h H) (i : MPos h) : Prop :=
  selCol σ R i.1 = i.2

instance {h H : ℕ} (σ : Seed h H) (R : Key h H) (i : MPos h) : Decidable (majSel σ R i) := by
  unfold majSel; infer_instance

/-- The compatible keys `R_i = {R ∈ R : i ∈ S(R)}`. -/
def majCompat {h H : ℕ} (σ : Seed h H) (i : MPos h) : Finset (Key h H) :=
  Finset.univ.filter fun R => majSel σ R i

/-- The conditional sampler for `R_i`, `i = (a⋆, b⋆)`: given independent uniform blocks
`r_t ∈ {−1,+1}^d`, replace `r_t` by `−r_t` whenever `sgn⟨r_t, v_{a⋆}⟩ ≠ b⋆_t`. -/
def majSampler {h H : ℕ} (σ : Seed h H) (i : MPos h) (R₀ : Key h H) : Key h H :=
  fun t => if Int.sign (ip (R₀ t) (rowVec σ i.1)) = ((i.2 t : ℤˣ) : ℤ) then R₀ t else -R₀ t

/-- The coins of `Query`: per block a flip coin (`true` = flipped), per coordinate of each block a
label of `H² + ⌈4 log₂ d⌉` bits, and a fresh key used only in the collision branch. -/
abbrev Coins (h H : ℕ) :=
  (Fin h → Bool) × (Fin h → Fin (dim H) → Fin (2 ^ labelBits H)) × Key h H

/-- Step (b): two labels collide within some block. -/
def Collision {h H : ℕ} (c : Coins h H) : Prop :=
  ∃ t : Fin h, ∃ k k' : Fin (dim H), k ≠ k' ∧ c.2.1 t k = c.2.1 t k'

instance {h H : ℕ} (c : Coins h H) : Decidable (Collision c) := by
  unfold Collision; infer_instance

/-- Step (c) for a flipped block `t`: with `F_t = b⋆_t⟨r_t, v_{a⋆}⟩`, among the coordinates `k`
with `r_{t,k} = b⋆_t v_{a⋆,k}` negate the `F_t` with the smallest labels (labels are distinct
when this step runs). -/
def flipBlock {h H : ℕ} (σ : Seed h H) (i : MPos h) (R : Key h H)
    (lab : Fin h → Fin (dim H) → Fin (2 ^ labelBits H)) (t : Fin h) : Fin (dim H) → ℤˣ :=
  let v := rowVec σ i.1
  let F := (((i.2 t : ℤˣ) : ℤ) * ip (R t) v).toNat
  fun k =>
    if R t k = i.2 t * v k ∧
        (Finset.univ.filter fun k' => R t k' = i.2 t * v k' ∧ lab t k' < lab t k).card < F
    then -R t k else R t k

/-- The output of `Query(i, R)` on coins `c`: `(fresh key, fail)` on a label collision, otherwise
`(Q, ok)` where `Q` keeps the retained blocks and replaces each flipped block by `flipBlock`.
(`true` is `ok`, `false` is `fail`.) -/
def queryMap {h H : ℕ} (σ : Seed h H) (i : MPos h) (R : Key h H) (c : Coins h H) :
    Key h H × Bool :=
  if Collision c then (c.2.2, false)
  else (fun t => if c.1 t then flipBlock σ i R c.2.1 t else R t, true)

/-- `Query(i, R)`: the law of `(Q, u)` under uniform coins (steps (a)–(d)). -/
noncomputable def majQuery {h H : ℕ} (σ : Seed h H) (i : MPos h) (R : Key h H) :
    PMF (Key h H × Bool) :=
  (PMF.uniformOfFintype (Coins h H)).map (queryMap σ i R)

/-- `(a, b) ∈ S⁺(Q)` (23): `b_t ⟨q_t, v_a⟩ ≥ −∆` for all `t ∈ [h]`. -/
def Reported {h H : ℕ} (σ : Seed h H) (Q : Key h H) (p : MPos h) : Prop :=
  ∀ t : Fin h, -shift H ≤ ((p.2 t : ℤˣ) : ℤ) * ip (Q t) (rowVec σ p.1)

instance {h H : ℕ} (σ : Seed h H) (Q : Key h H) (p : MPos h) : Decidable (Reported σ Q p) := by
  unfold Reported; infer_instance

/-- All column labels `{−1,+1}^h` in lexicographic order: coordinate `0` first, `−1 < +1`. -/
def colList (h : ℕ) : List (Fin h → ℤˣ) :=
  (List.finRange (2 ^ h)).map fun c t => if c.val.testBit (h - 1 - t.val) then 1 else -1

/-- `S⁺(Q)` enumerated in row order and, within a row, in lexicographic order of the column
labels. -/
def enumReported {h H : ℕ} (σ : Seed h H) (Q : Key h H) : List (MPos h) :=
  (List.finRange (2 ^ h)).flatMap fun a =>
    ((colList h).filter fun b => decide (Reported σ Q (a, b))).map fun b => (a, b)

/-- `Answer(D, Q)`: `none` (= abort) if `|S⁺(Q)| > 8m`, else `some β` with
`β = (D[a, b])_{(a,b) ∈ S⁺(Q)}` in the enumeration order. -/
def majAnswer {h H : ℕ} (σ : Seed h H) (D : MDB h) (Q : Key h H) : Option (List Bool) :=
  let L := enumReported σ Q
  if 8 * 2 ^ h < L.length then none else some (L.map fun p => D p.1 p.2)

/-- The XOR of a list of bits. -/
def xorList (l : List Bool) : Bool := l.foldr Bool.xor false

/-- `Hint(D, R) = ⊕_{a ∈ [m]} D[a, sgn(R v_a)]`. -/
def majHint {h H : ℕ} (σ : Seed h H) (D : MDB h) (R : Key h H) : Bool :=
  xorList ((List.finRange (2 ^ h)).map fun a => D a (selCol σ R a))

/-- `Decode(i, R, z, Q, u, ans)`: `⊥` (`none`) if `u = fail` or `ans = abort`; otherwise
associate the answer bits with the positions of `S⁺(Q)` in the server's order; `⊥` if some
position of `S(R) ∖ {i}` is absent; else `z ⊕ ⊕_{(a,b) ∈ S(R)∖{i}} β_{a,b}` (24). -/
def majDecode {h H : ℕ} (σ : Seed h H) (i : MPos h) (R : Key h H) (z : Bool) (Q : Key h H)
    (u : Bool) (ans : Option (List Bool)) : Option Bool :=
  match u, ans with
  | true, some β =>
      let L := enumReported σ Q
      let others : List (MPos h) := (List.finRange (2 ^ h)).filterMap fun a =>
        if ((a, selCol σ R a) : MPos h) = i then none else some (a, selCol σ R a)
      let look := others.map fun p => List.lookup p (L.zip β)
      if look.all Option.isSome then
        some (Bool.xor z (xorList (look.map fun o => o.getD false)))
      else none
  | _, _ => none

/-- The client's output `Decode(i, R, Hint(D, R), Q, u, Answer(D, Q))` on the query outcome
`p = (Q, u)`. -/
def majOutcome {h H : ℕ} (σ : Seed h H) (D : MDB h) (i : MPos h) (R : Key h H)
    (p : Key h H × Bool) : Option Bool :=
  majDecode σ i R (majHint σ D R) p.1 p.2 (majAnswer σ D p.1)

end ITPIRPreproc.MatchVec.Supplement


