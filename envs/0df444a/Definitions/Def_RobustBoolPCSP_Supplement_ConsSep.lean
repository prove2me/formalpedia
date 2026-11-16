-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_ConsSep
-- name    : RobustBoolPCSP_Supplement_ConsSep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:24:05.467736+00:00
-- url     : https://prove2.me/theorems/02b215fd-33c3-40f4-a70c-7bde506f3b25
-- title:
--   Above-average selectors, separating certificates, conservative separability and $\mathrm{CS}_{\mathrm{out}}$
-- statement:
--   Let $q=|A|$ and $\bar z=q^{-1}\sum_a z_a$ for $z\in\mathbb R^A$. An **above-average selector** is a map $\rho:\mathbb R^A\to A$ with $z_{\rho(z)}\ge\bar z$ for all $z$; an **argmax selector** returns a label of maximal score.
--
--   For a pair $(P,W)$ on $A$ of positive arity $r$, a **separating certificate** for $b\in A^r\setminus W$ is a real matrix $\omega=(\omega_{i,a})$ with
--
--   $$\sum_{i,a}|\omega_{i,a}|=1,\quad \sum_a\omega_{i,a}=0,\quad L_\omega(x)=\sum_i\omega_{i,x_i}\ge0\ (x\in P),\quad \sum_i\omega_i\cdot z_i\le0\ \text{whenever }\rho(z_i)=b_i\ \forall i.$$
--
--   A template with $q\ge2$ and output map $h$ is **conservative separable** if one above-average selector gives every tuple outside every positive-arity $W_j$ a certificate and every nullary pair has $P_j\subseteq W_j$; for $q=1$ it is conservative separable if $P_j\subseteq W_j$ for all $j$. $\mathrm{CS}_{\mathrm{out}}$ is the class of templates conservative separable for some output map.
--
--   This is the class of the randomized log-free algorithm (Theorem 5.14).
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §5.3, p.37, Definition 5.13 and the preceding paragraph; Theorem 5.19, p.41 (argmax selector)

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_Classes

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- `ρ : ℝ^A → A` is an **above-average selector** (§5.3, p.37): "For z ∈ R^A, write
z̄ = q⁻¹ Σ_a z_a, where q = |A|. An above-average selector is a map ρ : R^A → A satisfying
z_{ρ(z)} ≥ z̄ for every z." No measurability is required (p.39). -/
def IsAboveAvg {A : Type} [Fintype A] (ρ : (A → ℝ) → A) : Prop :=
  ∀ z : A → ℝ, (∑ a, z a) / Fintype.card A ≤ z (ρ z)

/-- `ρ` is an **argmax selector** (Theorem 5.19, p.41): "any selector returning a label of maximal
score with a fixed tie rule". -/
def IsArgmaxSel {A : Type} (ρ : (A → ℝ) → A) : Prop :=
  ∀ (z : A → ℝ) (a : A), z a ≤ z (ρ z)

/-- `ω` is a **separating certificate** for the tuple `b` (outside `W`) with respect to the strong
relation `P` and the selector `ρ` (Definition 5.13, p.37): "a real matrix ω = (ω_{i,a})_{i∈[r],a∈A}
satisfying Σ_{i,a} |ω_{i,a}| = 1, Σ_{a∈A} ω_{i,a} = 0 (i ∈ [r]), (39)
L_ω(x) := Σ^r_{i=1} ω_{i,x_i} ≥ 0 (x ∈ P), (40)
Σ^r_{i=1} ω_i · z_i ≤ 0 whenever z_1, …, z_r ∈ R^A satisfy ρ(z_i) = b_i for all i. (41)" -/
def IsSepCert {A : Type} [Fintype A] {r : ℕ} (ρ : (A → ℝ) → A) (P : Set (Fin r → A))
    (b : Fin r → A) (ω : Fin r → A → ℝ) : Prop :=
  (∑ i, ∑ a, |ω i a|) = 1 ∧ (∀ i, ∑ a, ω i a = 0) ∧ (∀ x ∈ P, 0 ≤ ∑ i, ω i (x i)) ∧
    ∀ z : Fin r → A → ℝ, (∀ i, ρ (z i) = b i) → ∑ i, ∑ a, ω i a * z i a ≤ 0

/-- The pair `(P, W)` **has separating certificates for `ρ`**: every tuple outside `W` has one
(Definition 5.13, p.37; Theorem 5.18, p.39; Theorem 5.19, p.41). -/
def HasSepCerts {A : Type} [Fintype A] {r : ℕ} (ρ : (A → ℝ) → A) (P W : Set (Fin r → A)) : Prop :=
  ∀ b, b ∉ W → ∃ ω : Fin r → A → ℝ, IsSepCert ρ P b ω

/-- The template `T` with output map `h` is **conservative separable** (Definition 5.13, p.37): "A
template with q ≥ 2 and output map h is conservative separable if one above-average selector ρ has
the following property: for every relation pair of positive arity, every tuple outside the
pulled-back relation W_j has a separating certificate, and every nullary relation pair satisfies
P_j ⊆ W_j. When q = 1, a template is called conservative separable if P_j ⊆ W_j for every j." -/
def ConsSep {ι A B : Type} [Fintype A] (T : Template ι A B) (h : A → B) : Prop :=
  (2 ≤ Fintype.card A →
    ∃ ρ : (A → ℝ) → A, IsAboveAvg ρ ∧
      ∀ j, (0 < T.r j → HasSepCerts ρ (T.P j) (pullback T h j)) ∧
        (T.r j = 0 → T.P j ⊆ pullback T h j)) ∧
  (Fintype.card A ≤ 1 → ∀ j, T.P j ⊆ pullback T h j)

/-- The class `CS_out` (Definition 5.13, p.37): "Write CS_out for the class of templates that are
conservative separable for some output map." -/
def InCSout {ι A B : Type} [Fintype A] (T : Template ι A B) : Prop :=
  ∃ h : A → B, ConsSep T h

end RobustBoolPCSP.Supplement


