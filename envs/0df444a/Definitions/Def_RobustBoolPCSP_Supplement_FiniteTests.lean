-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_FiniteTests
-- name    : RobustBoolPCSP_Supplement_FiniteTests
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:28:18.663838+00:00
-- url     : https://prove2.me/theorems/18b6ecdd-58c5-45af-ab9e-7c9ef8b4543c
-- title:
--   The modified finite-product tests and influences of §10.4
-- statement:
--   Fix rational $0<v\le1/10$; on $A=\{-1,0,1\}$ let $\nu_v(\pm1)=v/2$, $\nu_v(0)=1-v$. For fuzzy $F:\{-1,1\}^R\to\Delta(B)$ and $G:(A,\nu_v)^R\to\Delta(B)$:
--
--   1. **antipodal test**: uniform $U$, request $F(U)$, $F(-U)$, accept on an $H$-edge;
--   2. **erasure test**: uniform signs $U_i$, $M_i\sim\mathrm{Bernoulli}(v)$, $V_i=(2M_i-1)U_i$, $X_i=-M_iU_i$; request $F(U)$, $F(V)$, $G(X)$, accept if the colors contain an $H$-edge;
--   3. **equality test**: $X\sim\nu_v^R$, $Y$ obtained by resampling each coordinate from $\nu_v$ with probability $v^2$; accept if the colors of $G(X)$, $G(Y)$ agree.
--
--   The first two tests are modified by resampling each coordinate of every distinct requested word from its marginal with probability $v^4$; literal duplicate words share one color. Influences $\mathrm{Inf}^{\le D}_i$ are computed in the product bases $1,x$ (binary) and $1$, $x/\sqrt v$, $(x^2-v)/\sqrt{v(1-v)}$ (ternary).
--
--   These tests and influences state the low-influence bound Theorem 10.10.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §10.4, p.89, eq. (108)

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_GaussianTests

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

/-! Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…), §10.4, p.89. Binary words `{−1,1}^R` are `Fin R → Bool` (`true` = `1`,
`false` = `−1`); ternary words `A^R`, `A = {−1, 0, 1}`, are `Fin R → SignType`. -/

/-- The sign `±1` of a binary letter (`true` ↦ `1`, `false` ↦ `−1`). -/
def sgnB (b : Bool) : ℝ := if b then 1 else -1

/-- `ν_v` on `A = {−1, 0, 1}` (p.89): "ν_v(−1) = ν_v(1) = v/2, ν_v(0) = 1 − v." -/
noncomputable def nuV (v : ℝ) (x : SignType) : ℝ := if x = 0 then 1 - v else v / 2

/-- The resampling kernel of a binary letter: kept with probability `1 − σ`, otherwise redrawn from
its uniform marginal. -/
noncomputable def kerB (σ : ℝ) (x y : Bool) : ℝ := (1 - σ) * (if x = y then 1 else 0) + σ / 2

/-- The resampling kernel of a ternary letter: kept with probability `1 − σ`, otherwise redrawn from
`ν_v`. -/
noncomputable def kerT (v σ : ℝ) (x y : SignType) : ℝ :=
  (1 - σ) * (if x = y then 1 else 0) + σ * nuV v y

/-- The word kernel of independent coordinatewise binary resampling. -/
noncomputable def kerBW {R : ℕ} (σ : ℝ) (x y : Fin R → Bool) : ℝ := ∏ i, kerB σ (x i) (y i)

/-- The word kernel of independent coordinatewise ternary resampling. -/
noncomputable def kerTW {R : ℕ} (v σ : ℝ) (x y : Fin R → SignType) : ℝ := ∏ i, kerT v σ (x i) (y i)

/-- The rejection probability of the antipodal relation on two requested `F`-words: if the words are
equal they share one color (which is never an `H`-edge with itself), otherwise their colors are
drawn independently. -/
noncomputable def rejPair {R : ℕ} (F : (Fin R → Bool) → ZMod 5 → ℝ) (y₁ y₂ : Fin R → Bool) : ℝ :=
  if y₁ = y₂ then ∑ b, F y₁ b * (if hEdge b b then 0 else 1)
  else ∑ b, ∑ b', F y₁ b * F y₂ b' * (if hEdge b b' then 0 else 1)

/-- The rejection probability of the erasure relation on two requested `F`-words and one requested
`G`-word: equal `F`-words share one color; distinct requested colors are independent. -/
noncomputable def rejTriple {R : ℕ} (F : (Fin R → Bool) → ZMod 5 → ℝ)
    (G : (Fin R → SignType) → ZMod 5 → ℝ) (y₁ y₂ : Fin R → Bool) (y₃ : Fin R → SignType) : ℝ :=
  if y₁ = y₂ then ∑ b, ∑ b₃, F y₁ b * G y₃ b₃ * (if noEdge3 b b b₃ then 1 else 0)
  else ∑ b₁, ∑ b₂, ∑ b₃, F y₁ b₁ * F y₂ b₂ * G y₃ b₃ * (if noEdge3 b₁ b₂ b₃ then 1 else 0)

/-- The **modified antipodal test** (p.89): "Sample a uniform binary word U and request F(U),
F(−U); accept if the colors form an H-edge", modified by "independently resampling each coordinate
of every distinct requested word from its own marginal with probability σ = v⁴, before applying F".
"Literal duplicate positions share their requested word and color." Value: rejection probability. -/
noncomputable def modAntipodal {R : ℕ} (v : ℝ) (F : (Fin R → Bool) → ZMod 5 → ℝ) : ℝ :=
  ∑ U : Fin R → Bool, (1 / 2 : ℝ) ^ R *
    (let negU : Fin R → Bool := fun i => !U i
     if U = negU then ∑ y, kerBW (v ^ 4) U y * rejPair F y y
     else ∑ y₁, ∑ y₂, kerBW (v ^ 4) U y₁ * kerBW (v ^ 4) negU y₂ * rejPair F y₁ y₂)

/-- The **modified erasure test** (p.89): "Independently for each coordinate, draw a uniform sign U_i
and M_i ∼ Bernoulli(v), and set V_i = (2M_i − 1)U_i, X_i = −M_iU_i. Request F(U), F(V), G(X) and
accept if these colors contain an H-edge", with every distinct requested word resampled
coordinatewise with probability `σ = v⁴` from its own marginal (uniform for binary words, `ν_v` for
the ternary word). Value: rejection probability. -/
noncomputable def modErasure {R : ℕ} (v : ℝ) (F : (Fin R → Bool) → ZMod 5 → ℝ)
    (G : (Fin R → SignType) → ZMod 5 → ℝ) : ℝ :=
  ∑ U : Fin R → Bool, ∑ M : Fin R → Bool,
    (1 / 2 : ℝ) ^ R * (∏ i, (if M i then v else 1 - v)) *
      (let V : Fin R → Bool := fun i => if M i then U i else !U i
       let X : Fin R → SignType := fun i => if M i then (if U i then -1 else 1) else 0
       ∑ y₃, kerTW v (v ^ 4) X y₃ *
         (if U = V then ∑ y, kerBW (v ^ 4) U y * rejTriple F G y y y₃
          else ∑ y₁, ∑ y₂, kerBW (v ^ 4) U y₁ * kerBW (v ^ 4) V y₂ * rejTriple F G y₁ y₂ y₃))

/-- The **equality test** (p.89, left unmodified): "Sample X ∼ ν_v^R and obtain Y by independently
resampling each coordinate from ν_v with probability η = v². Request G(X), G(Y) and accept if the
colors agree." Equal words share one color (accepted). Value: rejection probability. -/
noncomputable def eqTest {R : ℕ} (v : ℝ) (G : (Fin R → SignType) → ZMod 5 → ℝ) : ℝ :=
  ∑ X : Fin R → SignType, ∑ Y : Fin R → SignType,
    (∏ i, nuV v (X i)) * kerTW v (v ^ 2) X Y *
      (if X = Y then 0 else ∑ b, ∑ b', G X b * G Y b' * (if b = b' then 0 else 1))

/-- The **average modified-test rejection** (p.89): the three tests, "each of weight 1/3". -/
noncomputable def avgModRej {R : ℕ} (v : ℝ) (F : (Fin R → Bool) → ZMod 5 → ℝ)
    (G : (Fin R → SignType) → ZMod 5 → ℝ) : ℝ :=
  (modAntipodal v F + modErasure v F G + eqTest v G) / 3

/-- The Fourier coefficient `f̂(S) = E[f(U) Π_{i∈S} U_i]` of `f` on the uniform binary cube (basis
`1, x` per coordinate, p.89). -/
noncomputable def fourierB {R : ℕ} (f : (Fin R → Bool) → ℝ) (S : Finset (Fin R)) : ℝ :=
  ∑ x : Fin R → Bool, (1 / 2 : ℝ) ^ R * f x * ∏ i ∈ S, sgnB (x i)

/-- The degree-`≤ D` influence `Inf^{≤D}_i(f)` on the binary cube: "the sum of squared coefficients
of degree at most D that use block i" (p.89). -/
noncomputable def infLeB {R : ℕ} (D : ℕ) (f : (Fin R → Bool) → ℝ) (i : Fin R) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin R) => i ∈ S ∧ S.card ≤ D), fourierB f S ^ 2

/-- The orthonormal basis (108) of `L²(A, ν_v)` (p.89): "1, ϕ₁(x) = x/√v,
ϕ₂(x) = (x² − v)/√(v(1 − v))", indexed by `0, 1, 2`. -/
noncomputable def phiT (v : ℝ) (s : Fin 3) (x : SignType) : ℝ :=
  if s = 0 then 1
  else if s = 1 then (x : ℝ) / Real.sqrt v
  else ((x : ℝ) ^ 2 - v) / Real.sqrt (v * (1 - v))

/-- The coefficient `f̂(σ) = E_{ν_v^R}[f(X) Π_i ϕ_{σ_i}(X_i)]` in the product basis. -/
noncomputable def fourierT {R : ℕ} (v : ℝ) (f : (Fin R → SignType) → ℝ) (σ : Fin R → Fin 3) : ℝ :=
  ∑ x : Fin R → SignType, (∏ i, nuV v (x i)) * f x * ∏ i, phiT v (σ i) (x i)

/-- The degree-`≤ D` influence on `(A, ν_v)^R`: the sum of `f̂(σ)²` over multi-indices `σ` using
coordinate `i` (`σ_i ≠ 0`) with at most `D` nonconstant factors (p.89). -/
noncomputable def infLeT {R : ℕ} (v : ℝ) (D : ℕ) (f : (Fin R → SignType) → ℝ) (i : Fin R) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Fin R → Fin 3 =>
      σ i ≠ 0 ∧ (Finset.univ.filter (fun j => σ j ≠ 0)).card ≤ D), fourierT v f σ ^ 2

/-- A finite fuzzy coloring: every value is a probability vector on `B = Z/5Z`. -/
def IsFuzzyFin {X : Type} (F : X → ZMod 5 → ℝ) : Prop :=
  ∀ x, (∀ b, 0 ≤ F x b) ∧ ∑ b, F x b = 1

end RobustBoolPCSP.Supplement


