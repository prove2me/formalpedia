-- Prove2me | Definitions.Def_RPLib_S3_Statements
-- name    : RPLib_S3_Statements
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:51:47.435407+00:00
-- url     : https://prove2.me/theorems/b55bb8ce-6c47-4d9b-97f4-584ff2157660
-- title:
--   The Eichler-Selberg trace formula, the arithmetic terms of the formula on $\Gamma_1(M)$
-- statement:
--   Definitions of the quantities in the Eichler-Selberg (Cohen-Oesterlé) trace formula for $T_n \langle \delta \rangle$ on $S_k(\Gamma_1(M))$: reduced positive definite binary quadratic forms of a given discriminant, counts of level vectors $v \in (\mathbb{Z}/M)^2$ of exact order $M$, Hurwitz class numbers, the Dedekind function $\psi(M) = M \prod_{\ell \mid M}(1 + 1/\ell)$, the character sums $\sum_{\chi(-1) = \varepsilon} \chi(z)$ in closed form, the scalar, elliptic, hyperbolic and Eisenstein terms $A_1, \dots, A_4$, the operators $T_{p^m}$, and the statement shapes of the trace formula.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Theorem 12.4.11

import Mathlib
import Definitions.Def_RPLib_S1_Hecke
import Definitions.Def_RPLib_S2_SymTrace
import Definitions.Def_RPLib_S2_EllFq
import Definitions.Def_RPLib_S2_TateNFB

/-!
# S3 frozen statement shapes (unit S3-RouteSpike)

Definitions of the S3 currency (reduced forms, level-vector counts, `ellCount`, Hurwitz class numbers, the
Cohen-Oesterle terms for `Γ₁(M)`), the operators `T_{p^m}` and `Φ`, and the S3 results as `Prop`s.
Nothing here is proved; each `Prop` names the unit that proves it (see `scratch/rp/S3_DESIGN.md`, section 7).

Numeric status (Python, `units/S3-RouteSpike/numgate.py` + `units/S3-NumCheck`):
* `ellG1` (the `ellCount` form of Cohen's elliptic term, with `δ⁻¹`) equals the Cohen-Oesterle `A2` for
  `Γ₁(M)`: 4050 cases, `M ≤ 12`, `k ≤ 6`, `n ≤ 18`, all `δ`, including `gcd(n, M) > 1`; the `δ` (not `δ⁻¹`)
  convention fails 1170 of them.
* `DWSExact` holds in 2683 cases (`q ≤ 125`, `M ≤ 13`), 381 of them supersingular.
* the four terms equal NumCheck's Cohen-Oesterle terms, checked there against q-expansion traces.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3

open RamanujanPetersson.Diamond RamanujanPetersson.Hecke RPLib

/-! ## Arithmetic currency -/

/-- `U_j(t,n)`: `U_0 = 1`, `U_1 = t`, `U_{j+2} = t U_{j+1} - n U_j`, the trace of `Sym^j` of a `2 × 2` matrix
with trace `t` and determinant `n` (`SymTrace.trace_symMat`). -/
def chebU (j : ℕ) (t n : ℤ) : ℤ := SymTrace.U j t n

/-- Reduced positive-definite binary quadratic forms `[a,b,c]` with `b² - 4ac = D` (imprimitive forms included):
`|b| ≤ a ≤ c`, and `b ≥ 0` when `|b| = a` or `a = c`. Empty unless `D < 0`.
Enumerated over `ℕ` ranges so that it evaluates (`|·|` and `Finset.Icc` on `ℤ` pick noncomputable instances). -/
def redForms (D : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (((Finset.range (D.natAbs + 1)) ×ˢ (Finset.range (2 * D.natAbs + 1)) ×ˢ (Finset.range (D.natAbs + 1))).image
      fun Q : ℕ × ℕ × ℕ => ((Q.1 : ℤ), (Q.2.1 : ℤ) - D.natAbs, (Q.2.2 : ℤ))).filter fun Q =>
    1 ≤ Q.1 ∧ Q.2.1 ^ 2 - 4 * Q.1 * Q.2.2 = D ∧ -Q.1 ≤ Q.2.1 ∧ Q.2.1 ≤ Q.1 ∧ Q.1 ≤ Q.2.2 ∧
      (0 ≤ Q.2.1 ∨ (Q.2.1 ≠ -Q.1 ∧ Q.1 ≠ Q.2.2))

/-- Order of the `SL₂(ℤ)`-stabiliser (including `±I`) of a reduced form. -/
def stabOrd (Q : ℤ × ℤ × ℤ) : ℕ :=
  if Q.1 = Q.2.1 ∧ Q.2.1 = Q.2.2 then 6 else if Q.2.1 = 0 ∧ Q.1 = Q.2.2 then 4 else 2

/-- The matrix of trace `t` and determinant `(t² - D)/4` whose fixed-point form is `Q = [a,b,c]`. -/
def gammaQ (Q : ℤ × ℤ × ℤ) (t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(t - Q.2.1) / 2, -Q.2.2; Q.1, (t + Q.2.1) / 2]

/-- `#{v ∈ (ℤ/M)² of exact order M : g v = δ' v}` (exact order written as `d • v ≠ 0` for `0 < d < M`). -/
def levelCount (M : ℕ) [NeZero M] (δ' : ZMod M) (g : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  (Finset.univ.filter fun v : Fin 2 → ZMod M =>
    (∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0) ∧
      (g.map (Int.castRingHom (ZMod M))).mulVec v = δ' • v).card

/-- The elliptic count: `Σ_{Q reduced, disc t² - 4n} levelCount M δ' (γ_Q) / #Stab(Q)`. It is `0` when
`t² ≥ 4n`, and `2 * ellCount 1 1 t n = H(4n - t²)`. -/
def ellCount (M : ℕ) [NeZero M] (δ' : ZMod M) (t : ℤ) (n : ℕ) : ℚ :=
  ∑ Q ∈ redForms (t ^ 2 - 4 * n), (levelCount M δ' (gammaQ Q t) : ℚ) / stabOrd Q

/-- Hurwitz class number `H(N)`: `Σ_{Q reduced, disc -N} 2/#Stab(Q)`, with `H(0) = -1/12`. -/
def hurwitzH (N : ℕ) : ℚ :=
  if N = 0 then -1 / 12 else ∑ Q ∈ redForms (-(N : ℤ)), (2 : ℚ) / stabOrd Q

/-- `Σ_{χ mod L, χ(-1) = ε} χ(z)` in closed form. -/
def charSum (L : ℕ) (z ε : ℤ) : ℚ :=
  if L ≤ 2 then (if ε = 1 ∧ Int.gcd z L = 1 then 1 else 0)
  else (Nat.totient L : ℚ) / 2 *
    ((if (z : ZMod L) = 1 then 1 else 0) + ε * (if (z : ZMod L) = -1 then 1 else 0))

/-- Dedekind `ψ(M) = M ∏_{l ∣ M} (1 + 1/l) = [SL₂(ℤ) : Γ₀(M)]`. -/
def dedekindPsi (M : ℕ) : ℚ := M * ∏ l ∈ M.primeFactors, (1 + 1 / (l : ℚ))

/-! ## The Cohen-Oesterle terms for `Tr(T_n ⟨δ⟩ | S_k(Γ₁(M)))` -/

/-- Scalar term `A1`. -/
def scalarG1 (M k n : ℕ) (δ : ZMod M) : ℚ :=
  if Nat.sqrt n * Nat.sqrt n = n then
    ((k : ℚ) - 1) / 12 * dedekindPsi M * (Nat.sqrt n : ℚ) ^ (k - 2) *
      charSum M ((δ.val : ℤ) * Nat.sqrt n) ((-1) ^ k)
  else 0

/-- Elliptic term `A2 = -Σ_{t² < 4n} U_{k-2}(t,n) ellCount_M(δ⁻¹, t, n)`. -/
def ellG1 (M : ℕ) [NeZero M] (k n : ℕ) (δ : ZMod M) : ℚ :=
  -∑ i ∈ Finset.range (4 * n + 1),
    (chebU (k - 2) ((i : ℤ) - 2 * n) n : ℚ) * ellCount M δ⁻¹ ((i : ℤ) - 2 * n) n

/-- Hyperbolic/parabolic term `A3`: `-1/2 Σ_{e ∣ n} min(e, n/e)^{k-1} Σ_{τ ∣ M} φ(g_τ) Σ_χ χ(δ y_τ)`,
written with the `g_τ` solutions `x mod M` of `x ≡ e (τ)`, `x ≡ n/e (M/τ)` (`g_τ = gcd(τ, M/τ)`). -/
def hypG1 (M k n : ℕ) (δ : ZMod M) : ℚ :=
  -(1 / 2) * ∑ e ∈ n.divisors, ((if e ≤ n / e then e else n / e : ℕ) : ℚ) ^ (k - 1) *
    ∑ τ ∈ M.divisors, (Nat.totient (Nat.gcd τ (M / τ)) : ℚ) / (Nat.gcd τ (M / τ) : ℚ) *
      ∑ x ∈ (Finset.range M).filter
          (fun x : ℕ => (x : ℤ) ≡ (e : ℤ) [ZMOD (τ : ℤ)] ∧ (x : ℤ) ≡ ((n / e : ℕ) : ℤ) [ZMOD ((M / τ : ℕ) : ℤ)]),
        charSum (M / Nat.gcd τ (M / τ)) ((δ.val : ℤ) * x) ((-1) ^ k)

/-- Eisenstein term `A4 = [k = 2] Σ_{e ∣ n, gcd(M, n/e) = 1} e` (trivial character only). -/
def eisG1 (M k n : ℕ) : ℚ :=
  if k = 2 then ∑ e ∈ n.divisors.filter (fun e => Nat.Coprime M (n / e)), (e : ℚ) else 0

/-- The full Cohen-Oesterle right-hand side for `Γ₁(M)`. -/
def traceFormulaG1 (M : ℕ) [NeZero M] (k n : ℕ) (δ : ZMod M) : ℚ :=
  scalarG1 M k n δ + ellG1 M k n δ + hypG1 M k n δ + eisG1 M k n

/-! ## Operators -/

section Ops

variable {M : ℕ} [NeZero M]

/-- `T_{p^m}` on `S_k(Γ₁(M))` for `p ∤ M`, by the Hecke recursion
`T_{p^{m+2}} = T_p T_{p^{m+1}} - p^{k-1} ⟨p⟩ T_{p^m}` (the recursion of S1-HALG's `heckePow`). -/
noncomputable def Tpow (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (k : ℤ) : ℕ → Module.End ℂ (S1 M k)
  | 0 => 1
  | 1 => heckeT p k
  | (m + 2) => heckeT p k * Tpow p hpM k (m + 1) -
      (((p : ℂ) ^ (k - 1)) • diamond k (unitP hpM)) * Tpow p hpM k m

/-- `Φ = [[T_p, -p^{k-1}⟨p⟩], [1, 0]]` on `S ⊕ S`. Its eigenvalues are the Hecke roots (`RootOfPhi`), and
`Tr Φ^m = Tr T_{p^m} - p^{k-1} Tr(⟨p⟩ T_{p^{m-2}})` (`TracePhiPow`). -/
noncomputable def phiOp (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (k : ℤ) :
    Module.End ℂ (S1 M k × S1 M k) :=
  LinearMap.prod
    (heckeT p k ∘ₗ LinearMap.fst ℂ (S1 M k) (S1 M k) -
      ((p : ℂ) ^ (k - 1)) • (diamond k (unitP hpM) ∘ₗ LinearMap.snd ℂ (S1 M k) (S1 M k)))
    (LinearMap.fst ℂ (S1 M k) (S1 M k))

end Ops

/-! ## Point counts over finite fields -/

/-- `#{(E, P)/F : a_E = t}` with `P` of exact order `M`, counted on the Tate normal form `Y₁(M)(F)`
(for `M ≥ 4` pairs have no automorphisms and `Y₁(M)(F)` is in bijection with their classes, S2-TateNF). -/
noncomputable def pairCount (F : Type) [Field F] [DecidableEq F] (M : ℕ) (t : ℤ) : ℕ :=
  Nat.card {bc : F × F // bc ∈ TateNF.Y1 F M ∧ EllFq.trace (TateNF.tate bc.1 bc.2) = t}

/-- `Σ_{(E,P)/F} U_{k-2}(a_E, q)`, summed over the trace values `|t| ≤ 2q` (Hasse makes the range harmless). -/
noncomputable def pairSumU (F : Type) [Field F] [DecidableEq F] (M k q : ℕ) : ℤ :=
  ∑ t ∈ Finset.Icc (-(2 * q : ℤ)) (2 * q), (pairCount F M t : ℤ) * chebU (k - 2) t q

/-- The same sum over the pairs with `j(E) ∉ {0, 1728}` (`c₄ ≠ 0`, `c₆ ≠ 0`; the S4 base `U_j`). -/
noncomputable def pairSumU_j (F : Type) [Field F] [DecidableEq F] (M k q : ℕ) : ℤ :=
  ∑ t ∈ Finset.Icc (-(2 * q : ℤ)) (2 * q),
    (Nat.card {bc : F × F // bc ∈ TateNF.Y1 F M ∧ EllFq.trace (TateNF.tate bc.1 bc.2) = t ∧
      (TateNF.tate bc.1 bc.2).c₄ ≠ 0 ∧ (TateNF.tate bc.1 bc.2).c₆ ≠ 0} : ℤ) * chebU (k - 2) t q

/-! ## The S3 results as statements -/

/-- (S3-Hurwitz) Level one: `2 · ellCount_1(1, t, n) = H(4n - t²)`. -/
def Level1Ell : Prop :=
  ∀ (n : ℕ) (t : ℤ), t ^ 2 < 4 * n → 2 * ellCount 1 1 t n = hurwitzH (4 * n - t ^ 2).toNat

/-- (S3-ES-Wt2 at level one, or an elementary proof) Kronecker-Hurwitz:
`Σ_{t² ≤ 4n} H(4n - t²) = 2σ(n) - Σ_{d ∣ n} min(d, n/d)`. -/
def KroneckerHurwitz : Prop :=
  ∀ n : ℕ, 0 < n →
    ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ)),
        hurwitzH (4 * (n : ℤ) - t ^ 2).toNat =
      2 * ∑ d ∈ n.divisors, (d : ℚ) - ∑ d ∈ n.divisors, ((min d (n / d) : ℕ) : ℚ)

/-- (S3-HypParTerms for `k ≥ 3`, S3-ES-Wt2 for `k = 2`; assembly S3-EichlerSelberg) Eichler-Selberg / Cohen-
Oesterle for `Tr(T_{p^m} ⟨δ⟩ | S_k(Γ₁(M)))`. -/
def EichlerSelbergG1 : Prop :=
  ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ k : ℕ, 2 ≤ k → ∀ (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (m : ℕ)
    (δ : (ZMod M)ˣ),
    LinearMap.trace ℂ (S1 M (k : ℤ)) (Tpow p hpM (k : ℤ) m * diamond (k : ℤ) δ) =
      ((traceFormulaG1 M k (p ^ m) (δ : ZMod M) : ℚ) : ℂ)

/-- (S3-Matching) Power sums of `Φ`. -/
def TracePhiPow : Prop :=
  ∀ (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (k : ℤ),
    LinearMap.trace ℂ _ (phiOp p hpM k) = LinearMap.trace ℂ _ (heckeT (M := M) p k) ∧
    ∀ m : ℕ, LinearMap.trace ℂ _ (phiOp p hpM k ^ (m + 2)) =
      LinearMap.trace ℂ _ (Tpow p hpM k (m + 2)) -
        (p : ℂ) ^ (k - 1) * LinearMap.trace ℂ _ (diamond k (unitP hpM) * Tpow p hpM k m)

/-- (S3-Matching) Every Hecke root of a `T_p`, `⟨p⟩`-eigenform is an eigenvalue of `Φ`. -/
def RootOfPhi : Prop :=
  ∀ (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (k : ℤ) (F : S1 M k) (a c α : ℂ),
    F ≠ 0 → heckeT p k F = a • F → diamond k (unitP hpM) F = c • F →
      α ^ 2 - a * α + c * (p : ℂ) ^ (k - 1) = 0 → Module.End.HasEigenvalue (phiOp p hpM k) α

/-- (S3-DWS-Ordinary + S3-DWS-Supersingular, exact form; true numerically, NOT on the proof route)
`#{(E,P)/F_q : a_E = t} = ellCount_M(1,t,q) - [p ∣ t, m ≥ 2] p · ellCount_M(p⁻¹, t/p, q/p²)` for `t² < 4q`. -/
def DWSExact : Prop :=
  ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∀ (m : ℕ) (F : Type) [Field F]
    [Fintype F] [DecidableEq F], Fintype.card F = p ^ m → ∀ t : ℤ, t ^ 2 < 4 * p ^ m →
      (pairCount F M t : ℚ) = ellCount M 1 t (p ^ m) -
        (if (p : ℤ) ∣ t ∧ 2 ≤ m then p * ellCount M (p : ZMod M)⁻¹ (t / p) (p ^ (m - 2)) else 0)

/-- (S3-DWS-Ordinary, the form on the proof route) Ordinary traces: at most `ellCount`, and the total deficit
is bounded independently of `m`. -/
def DWSOrdinary : Prop :=
  ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∃ C : ℚ, ∀ (m : ℕ) (F : Type)
    [Field F] [Fintype F] [DecidableEq F], Fintype.card F = p ^ m →
      (∀ t : ℤ, ¬ (p : ℤ) ∣ t → (pairCount F M t : ℚ) ≤ ellCount M 1 t (p ^ m)) ∧
      ∑ t ∈ (Finset.Icc (-(2 * p ^ m : ℤ)) (2 * p ^ m)).filter (fun t => ¬ (p : ℤ) ∣ t),
        (ellCount M 1 t (p ^ m) - pairCount F M t) ≤ C

/-- (S3-DWS-Supersingular) Boundedly many supersingular pairs: `#{(E,P)/F_q : p ∣ a_E} ≤ C`. -/
def DWSSuper : Prop :=
  ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∃ C : ℕ, ∀ (m : ℕ) (F : Type)
    [Field F] [Fintype F] [DecidableEq F], Fintype.card F = p ^ m →
      ∑ t ∈ (Finset.Icc (-(2 * p ^ m : ℤ)) (2 * p ^ m)).filter (fun t => (p : ℤ) ∣ t), pairCount F M t ≤ C

/-- (S3-DWS-Supersingular, pure lattice combinatorics) The p-chain lemma:
`|ellCount_M(1,t,q) - p · ellCount_M(p⁻¹, t/p, q/p²)| ≤ C` for `p ∣ t`, uniformly in `m`. -/
def PChain : Prop :=
  ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∃ C : ℚ, ∀ (m : ℕ) (t : ℤ), (p : ℤ) ∣ t →
    |ellCount M 1 t (p ^ m) -
      (if 2 ≤ m then p * ellCount M (p : ZMod M)⁻¹ (t / p) (p ^ (m - 2)) else 0)| ≤ C

/-- (S3-Matching) Identity (I'): `Tr Φ^m + Σ_{(E,P)/F_q} U_{k-2}(a_E, q) - [k = 2](1 + q) = O(p^{m(k-2)/2}(1+m))`. -/
def IdentityI' : Prop :=
  ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ k : ℕ, 2 ≤ k → ∀ (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M), ∃ C : ℝ,
    ∀ (m : ℕ), 1 ≤ m → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], Fintype.card F = p ^ m →
      ‖LinearMap.trace ℂ _ (phiOp p hpM (k : ℤ) ^ m) + ((pairSumU F M k (p ^ m) : ℤ) : ℂ) -
          (if k = 2 then 1 + (p : ℂ) ^ m else 0)‖ ≤ C * Real.sqrt p ^ ((k - 2) * m) * (1 + m)

/-- (S3-Matching, the S4 interface) Identity (I') over the S4 base `j ∉ {0, 1728}`. -/
def IdentityI'_j : Prop :=
  ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ k : ℕ, 2 ≤ k → ∀ (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M), ∃ C : ℝ,
    ∀ (m : ℕ), 1 ≤ m → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], Fintype.card F = p ^ m →
      ‖LinearMap.trace ℂ _ (phiOp p hpM (k : ℤ) ^ m) + ((pairSumU_j F M k (p ^ m) : ℤ) : ℂ) -
          (if k = 2 then 1 + (p : ℂ) ^ m else 0)‖ ≤ C * Real.sqrt p ^ ((k - 2) * m) * (1 + m)

/-- (S3-Wt2RP for `k = 2`; S4 matching for `k ≥ 3`) Every eigenvalue of `Φ` has `|α| ≤ p^{(k-1)/2}`. -/
def PhiEigenBound (k : ℕ) : Prop :=
  ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (α : ℂ),
    Module.End.HasEigenvalue (phiOp p hpM (k : ℤ)) α → ‖α‖ ≤ Real.sqrt p ^ (k - 1)

end RamanujanPetersson.S3


