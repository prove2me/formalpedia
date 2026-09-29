-- Prove2me | Definitions.Def_CuspForm_AdelicLiftGamma1
-- name    : CuspForm_AdelicLiftGamma1
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/aa567d70-2558-501b-8197-02856064ba49
-- title:
--   Adelic lift of a weight-two cusp form on Γ1​(M)
-- statement:
--   Fix a natural number $M$, a cusp form $g$ of weight $2$ on $\Gamma_1(M)$, and a function $\varphi$ on the adelic group $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ (the group [`AutomorphicForm.AdelicGL2`](../def/AutomorphicForm_AdelicLsXi.html#L12) attached to $\mathcal{O}_{\mathbb{Q}}$ and $\mathbb{Q}$) with values in $\mathbb{C}$. The predicate [`CuspForm.IsAdelicLiftOfGamma1 g φ`](../def/CuspForm_AdelicLiftGamma1.html#L14) is the conjunction of three conditions. First, $\varphi(\gamma x)=\varphi(x)$ for every $\gamma\in\mathrm{GL}_2(\mathbb{Q})$, pushed into the adelic group by [`AutomorphicForm.globalPoints`](../def/AutomorphicForm_AdelicLsXi.html#L15), and every $x$. Second, $\varphi(xu)=\varphi(x)$ for every $x$ and every $u$ in the image under [`AdelicDock.finEmbed`](../def/AdelicDock_LocalEmbedding.html#L145) (the embedding with trivial archimedean component) of the subgroup [`NumberField.AdelicLevel.finiteLevelOne`](../def/NumberField_AdelicLevel.html#L418) of $\mathrm{GL}_2$ of the finite adeles at the ideal [`AdelicDock.ratLevel M`](../def/AdelicDock_LocalEmbedding.html#L303) $=(M)$: that subgroup consists of those $u$ for which both $u$ and $u^{-1}$ have all entries integral at every finite place, lower-left entry of valuation at most the bound attached to $(M)$ at each place, and lower-right entry congruent to $1$ in the same sense. Third, for every $h$ whose finite part [`NumberField.AdelicLevel.glFin`](../def/NumberField_AdelicLevel.html#L194) is trivial and whose real component [`LanglandsTunnell.ratArchGL2 h`](../def/LanglandsTunnell_DeltaLift.html#L16) lies in `Matrix.GLPos (Fin 2) ℝ`, one has $\varphi(h)=\bigl(g\mid_2 \mathrm{ratArchGL2}\,h\bigr)(i)$, the weight-$2$ slash action evaluated at $i\in\mathfrak{H}$.
--
--   The module is a predicate on a given pair $(g,\varphi)$: no existence or uniqueness of a lift is asserted, nor anything about a central character. Three accompanying lemmas, `left_inv`, `level_inv` and `apply_eq`, are the projections onto the three clauses. No hypothesis $M\neq 0$ is imposed; for $M=0$ the ideal $(M)$ is zero and the level subgroup degenerates accordingly.
--
--   **Relation to Mathlib.** The classical side uses Mathlib's `CuspForm` for `CongruenceSubgroup.Gamma1` and Mathlib's weight-$k$ slash action `∣[k]`; the adelic side (the level subgroups, the finite/archimedean component maps and the embeddings) and the lifting predicate itself are the project's own notions, Mathlib having no adelic automorphic forms on $\mathrm{GL}_2$.
--
--   **Where it is used.** The predicate is the dictionary between weight-two cusp forms on $\Gamma_1(M)$ and functions on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, used where Hecke eigenvalue data of modular forms is transported to the adelic setting in the Langlands–Tunnell and modularity parts of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_AdelicLiftGamma1.lean

import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CuspForm

variable {M : ℕ}

open scoped ModularForm in

def IsAdelicLiftOfGamma1 (g : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) : Prop :=
  (∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = φ x) ∧
    (∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel M),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = φ x) ∧
    ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
          φ h = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I

theorem IsAdelicLiftOfGamma1.left_inv {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφg : IsAdelicLiftOfGamma1 g φ)
    (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = φ x :=
  hφg.1 γ x

theorem IsAdelicLiftOfGamma1.level_inv {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφg : IsAdelicLiftOfGamma1 g φ) :
    ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel M),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = φ x :=
  hφg.2.1

open scoped ModularForm in

theorem IsAdelicLiftOfGamma1.apply_eq {g : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφg : IsAdelicLiftOfGamma1 g φ)
    (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
    (hfin : NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    φ h = ((⇑g) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I :=
  hφg.2.2 h hfin hpos

end CuspForm

end


