-- Prove2me | Definitions.Def_MICPRep_Periodic_Setting
-- name    : MICPRep_Periodic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:26.414068+00:00
-- url     : https://prove2.me/theorems/19439b8b-3f09-4bf7-81e9-5b825e6576f3
-- title:
--   Definitions 1.1, 1.2, 1.4, 1.7, 3.2, 3.3, 4.1, 5.1, 5.2, 6.1–6.5 and (4.4) — MICP formulations, binary and rational MICP-R sets, periodic sets, MICP diameter, nearly periodic formulations, aff_ℤ
-- statement:
--   This module fixes the objects of Lubin, Vielma and Zadik's theory of mixed-integer convex representability. Throughout, $n, p, d \in \mathbb Z_+ = \{0,1,2,\dots\}$, points of $\mathbb R^{n+p+d}$ are written $(x, y, z)$ with $x \in \mathbb R^n$ the original variables, $y \in \mathbb R^p$ continuous auxiliary variables and $z \in \mathbb R^d$ the variables required to be integer, and $\mathbb Z^d \subseteq \mathbb R^d$ is the integer lattice.
--
--   1. **MICP formulation (Definition 1.1).** A closed convex set $M \subseteq \mathbb R^{n+p+d}$ (with $d$) *induces an MICP formulation* of $S \subseteq \mathbb R^n$ when
--   $$x \in S \iff \exists\, y \in \mathbb R^p,\ z \in \mathbb Z^d:\ (x, y, z) \in M.$$
--   2. **Index set and $z$-projected sets (Definition 4.1).** $I = \mathrm{proj}_z(M)$, the projection of all of $M$ (not only of its integer slice), and $A_z = \mathrm{proj}_x(M \cap (\mathbb R^{n+p} \times \{z\}))$.
--   3. **Representability.** $S$ is *MICP-R* (Definition 1.2) if some such $M$ exists; *binary MICP-R* (Definition 1.4) if moreover $\mathrm{proj}_z(M \cap (\mathbb R^{n+p}\times\mathbb Z^d)) \subseteq \{0,1\}^d$.
--   4. **Recession cone (Definition 3.2).** $C_\infty = \{r : x + \lambda r \in C\ \forall x \in C,\ \lambda \ge 0\}$, of the set itself, not of its closure (the published characteristic cone).
--   5. **Rationally unbounded (Definition 5.1).** $I \subseteq \mathbb R^d$ is rationally unbounded if for every $d'$ and every rational affine map $z \mapsto Az + b$ ($A \in \mathbb Q^{d'\times d}$, $b \in \mathbb Q^{d'}$), the image $I'$ is bounded or $\mathbb Z^{d'} \cap (I'_\infty \setminus \{0\}) \neq \emptyset$. $S$ is *rational MICP-R* (Definition 5.2) if it has an MICP formulation whose index set is rationally unbounded.
--   6. **Periodic (Definition 1.7).** $S$ is periodic if there is $u \in \mathbb R^n \setminus \{0\}$ with $x + \lambda u \in S$ for all $x \in S$ and $\lambda \in \mathbb N = \{1,2,\dots\}$.
--   7. **MICP diameter (Definitions 3.3, 6.1).** $D(C) = \sup\{\|x - x'\|_2 : x, x' \in C\}$ and $D_{\mathrm{MICP}}(M) = \sup_{z \in I \cap \mathbb Z^d} D(A_z)$, both in $[0, \infty]$.
--   8. **Nearly periodic (Definition 6.2).** The formulation is nearly periodic if there are $u \in \mathbb R^n\setminus\{0\}$ and $r \in \mathbb Z^d \cap (I_\infty \setminus\{0\})$ with
--   $$x + \lambda u \in \mathrm{cl}(A_{z+\lambda r}) \qquad \forall \lambda \in \mathbb Z_+,\ z \in \mathbb Z^d \cap I,\ x \in A_z.$$
--   9. **Rational affine hull (Definition 6.3).** $\mathrm{aff}_{\mathbb Z}(I) = \mathrm{aff}(I \cap \mathbb Z^d)$ and $I_{\mathbb Z} = I \cap \mathrm{aff}_{\mathbb Z}(I)$; dimensions of affine sets are integers with $\dim \emptyset = -1$. A *rational affine subspace* is a nonempty affine subspace spanned by its rational points; $\mathbb R^k \times \{0\}^{d-k}$ is the coordinate subspace; the slab is $\{z : l \le z_1 \le u\}$.
--   10. **Unimodular matrices (Definition 6.4)** are the units of $\mathbb Z^{d\times d}$, and the **support function (Definition 6.5)** is $\sigma_A(c) = \sup\{c^{\mathsf T}x : x \in A\} \in \mathbb R\cup\{\pm\infty\}$.
--   11. **The lifted formulation (4.4).** For sets $\tilde S_1, \dots, \tilde S_k \subseteq \mathbb R^{n+q}$, $T_i = \{(w, w_0) : w \in \tilde S_i,\ \|w\|_2^2 \le w_0\}$ and $M = \mathrm{conv}\bigl(\bigcup_i T_i \times \{e(k,i)\}\bigr) \subseteq \mathbb R^{n+(q+1)+k}$.
--
--   These objects carry every statement of the paper's structural theory of rational MICP-R sets, from the binary characterization (Proposition 4.2) to the main decomposition theorem (Theorem 5.1).
--
--   **Formalization Note** $x$ lives in `EuclideanSpace ℝ (Fin n)`, so norms and the extended diameter `Metric.ediam` are Euclidean; $y$ and $z$ live in `Fin p → ℝ`, `Fin d → ℝ`. Diameters are in `ℝ≥0∞`, so an unbounded set has diameter $+\infty$. Coordinates are $0$-based: $z_1$ is the coordinate of index $0$, and $\mathbb R^k \times\{0\}^{d-k}$ is $\{z : z_i = 0 \text{ for } i \ge k\}$. `zProj M z` is defined for every $z$ (empty off $I$). Rational affine maps are $\mathbb Q$-matrices with $\mathbb Q$-offsets; the inverse of an invertible one is written `ratAffInv`. In (4.4) the norm $\|w\|_2^2$ of $w = (x, y')$ is $\|x\|_2^2 + \sum_j y_j'^2$, and $w_0$ is the last continuous coordinate. $\sup_{\emptyset} = 0$ in $D_{\mathrm{MICP}}$, which only matters for $S = \emptyset$.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, pp. 2–4, 8–10, 14, 21, 24, 28, Definitions 1.1, 1.2, 1.4, 1.7, 3.2, 3.3, 4.1, 5.1, 5.2, 6.1–6.5, formulation (4.4)

import Mathlib
import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- The space `ℝⁿ` of the original variables `x`, with the Euclidean norm `‖·‖₂`. -/
abbrev Pt (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The ambient space `ℝⁿ⁺ᵖ⁺ᵈ` of an MICP formulation, with points `(x, y, z)`:
`x ∈ ℝⁿ` (original variables), `y ∈ ℝᵖ` (continuous auxiliaries), `z ∈ ℝᵈ` (integer variables). -/
abbrev Ambient (n p d : ℕ) := Pt n × (Fin p → ℝ) × (Fin d → ℝ)

/-- The integer lattice `ℤᵈ ⊆ ℝᵈ`. -/
def intLattice (d : ℕ) : Set (Fin d → ℝ) :=
  Set.range (fun k : Fin d → ℤ => fun i => (k i : ℝ))

/-- The rational points `ℚᵈ ⊆ ℝᵈ`. -/
def ratPoints (d : ℕ) : Set (Fin d → ℝ) :=
  Set.range (fun q : Fin d → ℚ => fun i => (q i : ℝ))

/-- Definition 1.1, p. 2: `M ⊆ ℝⁿ⁺ᵖ⁺ᵈ` is a closed convex set and the pair `(M, d)` induces an
MICP formulation of `S ⊆ ℝⁿ`: `x ∈ S ⇔ ∃ y ∈ ℝᵖ, z ∈ ℤᵈ, (x, y, z) ∈ M` (1.1). -/
def Induces {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n)) : Prop :=
  IsClosed M ∧ Convex ℝ M ∧ ∀ x : Pt n, x ∈ S ↔ ∃ y : Fin p → ℝ, ∃ z ∈ intLattice d, (x, y, z) ∈ M

/-- Definition 4.1, p. 9: the index set `I = proj_z(M)` (projection of all of `M`). -/
def indexSet {n p d : ℕ} (M : Set (Ambient n p d)) : Set (Fin d → ℝ) :=
  (fun q : Ambient n p d => q.2.2) '' M

/-- Definition 4.1, p. 9: the `z`-projected set `A_z = proj_x(M ∩ (ℝⁿ⁺ᵖ × {z}))`
(empty when `z ∉ I`). -/
def zProj {n p d : ℕ} (M : Set (Ambient n p d)) (z : Fin d → ℝ) : Set (Pt n) :=
  {x | ∃ y : Fin p → ℝ, (x, y, z) ∈ M}

/-- Definition 1.2, p. 2: `S` is MICP representable. -/
def IsMICPR {n : ℕ} (S : Set (Pt n)) : Prop :=
  ∃ (p d : ℕ) (M : Set (Ambient n p d)), Induces M S

/-- Definition 1.4, p. 3: `S` is binary MICP-R: some closed convex `M` induces an MICP formulation
of `S` and `proj_z(M ∩ (ℝⁿ⁺ᵖ × ℤᵈ)) ⊆ {0, 1}ᵈ`. -/
def IsBinaryMICPR {n : ℕ} (S : Set (Pt n)) : Prop :=
  ∃ (p d : ℕ) (M : Set (Ambient n p d)), Induces M S ∧
    ∀ q ∈ M, q.2.2 ∈ intLattice d → ∀ i : Fin d, q.2.2 i = 0 ∨ q.2.2 i = 1

/-- Definition 3.2, p. 8: the recession cone `C∞ = {r : x + λ r ∈ C ∀ x ∈ C, λ ≥ 0}` of a set
(not of its closure). This is the published `Grunbaum2003.characteristicCone`. -/
abbrev recCone {d : ℕ} (C : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  Grunbaum2003.characteristicCone C

/-- A rational affine map `ℝᵈ → ℝᵈ'`, `z ↦ A z + b` with `A ∈ ℚ^{d'×d}`, `b ∈ ℚ^{d'}`. -/
def ratAff {d d' : ℕ} (A : Matrix (Fin d') (Fin d) ℚ) (b : Fin d' → ℚ) (z : Fin d → ℝ) :
    Fin d' → ℝ :=
  (A.map (fun q : ℚ => (q : ℝ))) *ᵥ z + fun i => (b i : ℝ)

/-- The inverse `z ↦ A⁻¹ (z − b)` of an invertible rational affine map `ratAff A b`
(meaningful when `IsUnit A`). -/
noncomputable def ratAffInv {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  ratAff A⁻¹ (-(A⁻¹ *ᵥ b))

/-- Definition 5.1, p. 14: `I ⊆ ℝᵈ` is rationally unbounded: for every `d'` and every rational
affine image `I' ⊆ ℝ^{d'}` of `I`, either `I'` is bounded or `ℤ^{d'} ∩ (I'∞ ∖ {0}) ≠ ∅`. -/
def IsRationallyUnbounded {d : ℕ} (I : Set (Fin d → ℝ)) : Prop :=
  ∀ (d' : ℕ) (A : Matrix (Fin d') (Fin d) ℚ) (b : Fin d' → ℚ),
    Bornology.IsBounded (ratAff A b '' I) ∨
      ∃ r ∈ intLattice d', r ≠ 0 ∧ r ∈ recCone (ratAff A b '' I)

/-- Definition 5.2, p. 14: `(M, d)` induces a rational MICP formulation of `S`. -/
def IsRationalFormulation {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n)) : Prop :=
  Induces M S ∧ IsRationallyUnbounded (indexSet M)

/-- Definition 5.2, p. 14: `S` is rational MICP-R. -/
def IsRationalMICPR {n : ℕ} (S : Set (Pt n)) : Prop :=
  ∃ (p d : ℕ) (M : Set (Ambient n p d)), IsRationalFormulation M S

/-- Definition 1.7, p. 4: `S` is periodic: some `u ≠ 0` has `x + λ u ∈ S` for all `x ∈ S` and
`λ ∈ ℕ = {1, 2, …}`. -/
def IsPeriodic {n : ℕ} (S : Set (Pt n)) : Prop :=
  ∃ u : Pt n, u ≠ 0 ∧ ∀ x ∈ S, ∀ k : ℕ, 1 ≤ k → x + (k : ℝ) • u ∈ S

/-- Definition 6.1, p. 21 (with Definition 3.3, p. 8): the MICP diameter
`D_MICP(M) = sup_{z ∈ I ∩ ℤᵈ} D(A_z)`, with the Euclidean diameter `D`, valued in `[0, ∞]`
(`Metric.ediam` is the extended diameter `sup ‖x − x'‖₂`, `+∞` on unbounded sets). -/
noncomputable def micpDiam {n p d : ℕ} (M : Set (Ambient n p d)) : ℝ≥0∞ :=
  ⨆ z ∈ indexSet M ∩ intLattice d, Metric.ediam (zProj M z)

/-- Definition 6.2, p. 21: the formulation induced by `M` is nearly periodic: there are
`u ∈ ℝⁿ ∖ {0}` and `r ∈ ℤᵈ ∩ (I∞ ∖ {0})` with
`x + λ u ∈ cl(A_{z + λ r})` for all `λ ∈ ℤ₊`, `z ∈ ℤᵈ ∩ I`, `x ∈ A_z` (6.1). -/
def IsNearlyPeriodic {n p d : ℕ} (M : Set (Ambient n p d)) : Prop :=
  ∃ u : Pt n, u ≠ 0 ∧ ∃ r ∈ intLattice d, r ≠ 0 ∧ r ∈ recCone (indexSet M) ∧
    ∀ k : ℕ, ∀ z ∈ intLattice d ∩ indexSet M, ∀ x ∈ zProj M z,
      x + (k : ℝ) • u ∈ closure (zProj M (z + (k : ℝ) • r))

/-- `S` has a nearly periodic MICP formulation (Definition 6.2, p. 21). -/
def HasNearlyPeriodicFormulation {n : ℕ} (S : Set (Pt n)) : Prop :=
  ∃ (p d : ℕ) (M : Set (Ambient n p d)), Induces M S ∧ IsNearlyPeriodic M

/-- Definition 6.3, p. 21: the rational affine hull `aff_ℤ(I) = aff(I ∩ ℤᵈ)`. -/
def affZ {d : ℕ} (I : Set (Fin d → ℝ)) : AffineSubspace ℝ (Fin d → ℝ) :=
  affineSpan ℝ (I ∩ intLattice d)

/-- Definition 6.3, p. 21: `I_ℤ = I ∩ aff_ℤ(I)`. -/
def IZ {d : ℕ} (I : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  I ∩ (affZ I : Set (Fin d → ℝ))

open Classical in
/-- The dimension of an affine subspace, integer valued, with `dim ∅ = −1`. -/
noncomputable def affDim {d : ℕ} (F : AffineSubspace ℝ (Fin d → ℝ)) : ℤ :=
  if (F : Set (Fin d → ℝ)).Nonempty then (Module.finrank ℝ F.direction : ℤ) else -1

/-- The dimension `dim(C) = dim aff(C)` of a set `C ⊆ ℝᵈ` (`−1` for `C = ∅`). -/
noncomputable def setDim {d : ℕ} (C : Set (Fin d → ℝ)) : ℤ :=
  affDim (affineSpan ℝ C)

/-- A rational affine subspace: a nonempty affine subspace spanned by its rational points. -/
def IsRationalAffineSubspace {d : ℕ} (F : AffineSubspace ℝ (Fin d → ℝ)) : Prop :=
  (F : Set (Fin d → ℝ)).Nonempty ∧ F = affineSpan ℝ ((F : Set (Fin d → ℝ)) ∩ ratPoints d)

/-- The coordinate subspace `ℝᵏ × {0}^{d−k} = {z : z_{i} = 0 for every coordinate i > k}`
(coordinates are `0`-based in Lean, so `i.val ≥ k`). -/
def coordSubspace (d : ℕ) (k : ℤ) : Set (Fin d → ℝ) :=
  {z | ∀ i : Fin d, k ≤ (i.val : ℤ) → z i = 0}

/-- The slab `{z ∈ ℝᵈ : l ≤ z₁ ≤ u}` (`z₁` is the coordinate with `0`-based index `0`). -/
def slab (d : ℕ) (l u : ℤ) : Set (Fin d → ℝ) :=
  {z | ∀ i : Fin d, i.val = 0 → (l : ℝ) ≤ z i ∧ z i ≤ (u : ℝ)}

/-- An integer matrix acting on `ℝᵈ`. -/
def intMatVec {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ) (v : Fin d → ℝ) : Fin d → ℝ :=
  (U.map (fun k : ℤ => (k : ℝ))) *ᵥ v

/-- Definition 6.4, p. 24: `U ∈ ℤ^{d×d}` is unimodular (invertible with `Uℤᵈ = U⁻¹ℤᵈ = ℤᵈ`),
i.e. a unit of the integer matrix ring. -/
def IsUnimodular {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  IsUnit U

/-- Definition 6.5, p. 28: the support function `σ_A(c) = sup {cᵀx : x ∈ A}` in `ℝ ∪ {±∞}`
(`σ_∅ = −∞`). -/
noncomputable def supportFn {n : ℕ} (A : Set (Pt n)) (c : Pt n) : EReal :=
  ⨆ x ∈ A, ((inner ℝ c x : ℝ) : EReal)

/-- The formulation (4.4) of Proposition 4.2, pp. 10–11. Given sets `S̃ᵢ ⊆ ℝⁿ⁺ᵠ`, `i ∈ ⟦k⟧`
(points `w = (x, y')` with `x ∈ ℝⁿ`, `y' ∈ ℝᵠ`), let
`Tᵢ = {(w, w₀) ∈ ℝⁿ⁺ᵠ⁺¹ : w ∈ S̃ᵢ, ‖w‖²₂ ≤ w₀}` with `‖w‖²₂ = ‖x‖²₂ + Σⱼ y'ⱼ²`, and
`M = conv(⋃ᵢ Tᵢ × {e(k, i)}) ⊆ ℝⁿ⁺ᵖ⁺ᵏ`, `p = q + 1`; the continuous variables are
`y = (y', w₀) ∈ ℝ^{q+1}` (`w₀` last) and `e(k, i)` is the `i`-th unit vector. -/
def liftedHull {n q k : ℕ} (St : Fin k → Set (Pt n × (Fin q → ℝ))) :
    Set (Ambient n (q + 1) k) :=
  convexHull ℝ (⋃ i : Fin k,
    {v | ∃ w ∈ St i, ∃ w₀ : ℝ, ‖w.1‖ ^ 2 + ∑ j, (w.2 j) ^ 2 ≤ w₀ ∧
      v = (w.1, (Fin.snoc w.2 w₀ : Fin (q + 1) → ℝ), (Pi.single i 1 : Fin k → ℝ))})

end MICPRep.Periodic


