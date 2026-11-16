-- Prove2me | Definitions.Def_GPTIP632_Classical_Supplement_Triangular
-- name    : GPTIP632_Classical_Supplement_Triangular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:15:45.219105+00:00
-- url     : https://prove2.me/theorems/33ec57e0-462e-447c-bd18-2fc8e32401a7
-- title:
--   Decidability, space classes, base-four coordinates and computable presentations
-- statement:
--   The comparison promise problem is the exact-rational definition already used in Lemma G.2. A promise problem is decidable if a Mathlib-Computable total Boolean function accepts its yes-set and rejects its no-set. A language lies in DSPACE(f) when an empty-oracle OTM halts on every input, decides it, and uses at most $C f(n)+C$ cells for a single constant $C$. The unary hierarchy property is membership of $\{1^n:n\in T\}$ in DSPACE($2^{n^2}$) and nonmembership in DSPACE($2^{cn}$) for every natural $c$; natural constants are cofinal in the real constants. The coordinate is the convergent sum $v_T=\sum_{i\in T}4^{-i-1}$. Computable linear presentations use finitely many linear inequalities with computable real coefficients. Computable PSD presentations use finitely many Hermitian coefficient matrices with computable real and imaginary parts and cone $\{x:\sum_i x_iM_i\succeq0\}$. Units and gate entries are computable, and computability of an isomorphism requires entries of both its forward and inverse matrices. Computable reals reuse DetParamSVP.IsComputableReal: a computable rational approximation within $2^{-r}$ for every positive $r$; asking also for $r=0$ is equivalent.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, pp.14, 17–19, 22–23, 28, 32–35 (PDF pp.16, 19–21, 24–25, 30, 34–37), Examples B.3, B.5, B.17–B.23, Definitions D.3–D.4, F.1, §G

import Mathlib
import Definitions.Def_GPTIP632_Classical_Supplement_Classes
import Definitions.Def_GPTIP632_Classical_Supplement_BinaryComparison
import Definitions.Def_DetParamSVP_ComputableReal

set_option autoImplicit false

/-!
# The promise problem `L_v`, decidability, space classes, `v_T`, computable presentations

Kishor Bharti, *Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical
Theories*, STOC 2027 submission #632 (October 2026), §A (p.12, PDF p.14), §G.1 (p.32, PDF p.34),
Lemma G.2 (p.33, PDF p.35), Fact G.6 and Theorem G.7 (p.35, PDF p.37).

Computable reals are the published `DetParamSVP.IsComputableReal`; decidability is decidability by
a Mathlib-`Computable` total function; space is the space of the published machine model
`QAdvFew.PoQOracle.OTM` run with the empty oracle (input cells counted).
-/

noncomputable section

namespace GPTIP632.Classical.Supplement

open GPTIP632.Classical Matrix KTUnitary.Synth QAlgorithms.Complexity QAdvFew.PoQOracle
open scoped ComplexOrder

attribute [local instance] _root_.Classical.propDecidable

/-- The binary fraction `t̄ = ∑_{j=1}^{|t|} t_j 2^{-j}` of a bit string (first bit most
significant), in `[0, 1)`. -/
def tbar (t : Str) : ℝ := (binaryFraction t : ℝ)

/-- The comparison promise problem, reusing the exact-rational definition. -/
def Lv (v : ℝ) : KTUnitary.Synth.PromiseProblem := comparisonProblem v

/-- A promise problem is **decidable** (§A, p.12) if some algorithm that halts on every input
accepts every string of `L_yes` and rejects every string of `L_no`: here, a Mathlib-`Computable`
total function `Str → Bool`. -/
def DecidablePP (L : KTUnitary.Synth.PromiseProblem) : Prop :=
  ∃ f : Str → Bool, Computable f ∧ (∀ x ∈ L.1, f x = true) ∧ (∀ x ∈ L.2, f x = false)

/-- **`DSPACE(f)`** for a language `A` (§A; Fact G.6): a machine (empty oracle) that halts on every
input `x` within space `C · f(|x|) + C` for a constant `C`, accepting exactly the strings of `A`. -/
def InDSPACE (A : Set Str) (f : ℕ → ℕ) : Prop :=
  ∃ (M : OTM) (C : ℕ), ∀ x : Str, ∃ T : ℕ, M.result O₀ x T ≠ none ∧ M.space O₀ x T ≤ C * f x.length + C ∧
    (M.result O₀ x T = some true ↔ x ∈ A)

/-- The unary language `{1^n : n ∈ T}`. -/
def unaryLang (T : Set ℕ) : Set Str := {x | ∃ n ∈ T, x = unary n}

/-- The **unary space hierarchy property** of Fact G.6: `{1^n : n ∈ T} ∈ DSPACE(2^{n²})` and
`∉ DSPACE(2^{cn})` for every constant `c`. -/
def UnaryHierarchy (T : Set ℕ) : Prop :=
  InDSPACE (unaryLang T) (fun n => 2 ^ (n ^ 2)) ∧ ∀ c : ℕ, ¬ InDSPACE (unaryLang T) (fun n => 2 ^ (c * n))

/-- `v_T = ∑_{i ∈ T} 4^{-i-1}` (Theorem G.7). -/
def vT (T : Set ℕ) : ℝ := ∑' i : ℕ, if i ∈ T then (1 / 4 : ℝ) ^ (i + 1) else 0

/-! ### Computable presentations (Theorem G.7 (i)) -/

/-- Every state cone has a finite description by linear constraints with computable coefficients:
for each system finitely many functionals `F_j` with computable coordinates and
`V⁺ = {x : F_j(x) ≥ 0 ∀ j}`. -/
def LinearComputableCones (G : Theory) : Prop :=
  ∀ A : G.C.Sys, ∃ (m : ℕ) (F : Fin m → (G.C.sys A).ι → ℝ),
    (∀ j k, DetParamSVP.IsComputableReal (F j k)) ∧
    ∀ x, x ∈ (G.C.sys A).cone ↔ ∀ j, 0 ≤ pair (F j) x

/-- Every state cone has a finite description by a positive-semidefinite constraint with
computable coefficients: for each system Hermitian-coefficient matrices `M_k` with computable real
and imaginary parts of all entries and `V⁺ = {x : ∑_k x_k M_k ⪰ 0}`. -/
def PSDComputableCones (G : Theory) : Prop :=
  ∀ A : G.C.Sys, ∃ (N : ℕ) (M : (G.C.sys A).ι → Matrix (Fin N) (Fin N) ℂ),
    (∀ k, (M k).IsHermitian) ∧
    (∀ k a b, DetParamSVP.IsComputableReal (M k a b).re ∧ DetParamSVP.IsComputableReal (M k a b).im) ∧
    ∀ x, x ∈ (G.C.sys A).cone ↔ (∑ k, ((x k : ℝ) : ℂ) • M k).PosSemidef

/-- The unit effects and the verifier's gates have computable entries. -/
def ComputableUnitsGates (G : Theory) : Prop :=
  (∀ (A : G.C.Sys) k, DetParamSVP.IsComputableReal ((G.C.sys A).unit k)) ∧
  ∀ g o i j, DetParamSVP.IsComputableReal (G.gate g o i j)

/-- An isomorphism of theories with computable entries. -/
def TheoryIso.Computable {G G' : Theory} (φ : TheoryIso G G') : Prop :=
  (∀ A k l, DetParamSVP.IsComputableReal (φ.map A k l)) ∧
  (∀ A k l, DetParamSVP.IsComputableReal (φ.inv A k l))

end GPTIP632.Classical.Supplement

end


