-- Prove2me | Definitions.Def_LanglandsTunnell_RSCarrierSplit
-- name    : LanglandsTunnell_RSCarrierSplit
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/9c947e08-7d53-505c-9fbb-4d57877f089c
-- title:
--   Archimedean Haar measure and finite factor for adelic GL₂
-- statement:
--   Two concrete objects attached to $\mathrm{GL}_2$ over $\mathbb{Q}$ are defined. First, [`RSCarrier.archMeasure`](../def/LanglandsTunnell_RSCarrierSplit.html#L11) is a measure on $\mathrm{GL}_2(\mathbb{R})$, taken with respect to the Borel $\sigma$-algebra of the group (supplied explicitly rather than through an instance). It is the push-back along the entrywise inclusion $g \mapsto (g_{ij})$ of $\mathrm{GL}_2(\mathbb{R})$ into the four-dimensional space $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}$ of Lebesgue measure (`volume`), weighted by the density $g \mapsto |\det g|^{-2}$ (converted into $[0,\infty]$ by `ENNReal.ofReal`). Thus no normalising constant is built in; left and right invariance, regularity and positivity of this measure are assertions about it and form no part of the definition.
--
--   Second, [`RSCarrier.finFactor`](../def/LanglandsTunnell_RSCarrierSplit.html#L17) assigns to an adelic matrix $g \in \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ an element of `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean-component homomorphism `AdelicLevel.glArch`, i.e. the subgroup of adelic matrices whose archimedean part is the identity. Its underlying element is $\big(\mathrm{archRealGLAt}\,(\mathrm{ratArchGL2}\,g)\big)^{-1} \cdot g$, where [`LanglandsTunnell.ratArchGL2`](../def/LanglandsTunnell_DeltaLift.html#L16) reads off the real component of $g$ at the default infinite place of $\mathbb{Q}$ (which is real, $\mathbb{Q}$ being totally real), transported through the identification of the completion at that place with $\mathbb{R}$, and `archRealGLAt` embeds $\mathrm{GL}_2(\mathbb{R})$ back into the adelic group at the same place. Membership in the subgroup is verified by an entrywise computation, using that $\mathbb{Q}$ has a single infinite place. Consequently $g$ factors as the image of its real component times `finFactor g`, and `finFactor g` has the same components as $g$ at every finite place.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient ingredients (Lebesgue measure on a finite product of copies of $\mathbb{R}$, `Measure.comap`, `withDensity`, and abstract Haar measures on locally compact groups); the explicit measure on $\mathrm{GL}_2(\mathbb{R})$ obtained here as Lebesgue measure on matrix entries with density $|\det|^{-2}$, and the splitting off of the real component of an adelic matrix, are the project's own.
--
--   **Where it is used.** These are the archimedean ingredients of the carrier on which Hecke eigensystems over $\mathbb{Q}$ are realised by smooth cuspidal automorphic functions on adelic $\mathrm{GL}_2$: the measure is the archimedean factor used in integration over $\mathrm{GL}_2(\mathbb{R})$, and the finite factor lets a function on the adelic group be analysed in a real variable at the unique infinite place, as needed for the lift of the discriminant cusp form and the Casimir and weight conditions in the Langlands–Tunnell input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_RSCarrierSplit.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_DeltaLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField AutomorphicForm

noncomputable section

namespace RSCarrier

def archMeasure : @Measure (GL (Fin 2) ℝ) (borel (GL (Fin 2) ℝ)) :=
  letI := borel (GL (Fin 2) ℝ)
  (Measure.comap (fun g : GL (Fin 2) ℝ => fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)
      (volume : Measure (Fin 2 → Fin 2 → ℝ))).withDensity
    fun g => ENNReal.ofReal (|(Matrix.GeneralLinearGroup.det g : ℝ)| ^ 2)⁻¹

def finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) : finiteAdelicGL2Subgroup ℚ :=
  ⟨(archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (LanglandsTunnell.ratArchGL2 g))⁻¹ * g, by
    rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_inv, inv_mul_eq_one]
    rw [show AdelicLevel.glArch (𝓞 ℚ) ℚ
        (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (LanglandsTunnell.ratArchGL2 g)) =
        archGLIncl ℚ default (glEquivOfRingEquiv
          (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm
          (LanglandsTunnell.ratArchGL2 g)) from glArch_adelicArchGLIncl ℚ _]
    refine Units.ext (Matrix.ext fun i j => funext fun v => ?_)
    obtain rfl : v = default := Subsingleton.elim v default
    refine (congrArg (fun u : GL (Fin 2) (default : InfinitePlace ℚ).Completion =>
        (u : Matrix (Fin 2) (Fin 2) (default : InfinitePlace ℚ).Completion) i j)
      (archComponent_archGLIncl_self ℚ default _)).trans ?_
    rw [glEquivOfRingEquiv_apply_entry]
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal _).symm_apply_apply _⟩

end RSCarrier

end


