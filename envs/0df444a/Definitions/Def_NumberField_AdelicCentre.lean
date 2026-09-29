-- Prove2me | Definitions.Def_NumberField_AdelicCentre
-- name    : NumberField_AdelicCentre
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/7adda3cc-49b8-5c52-85ac-8a98dddb44b7
-- title:
--   Centre of adelic GL2​, the quotient PGL2​, and its Haar measure
-- statement:
--   Throughout, $R$ is a Dedekind domain with fraction field $K$ (so that the adele ring `AdeleRing R K`, the product of the infinite and finite adele rings, is available) and $G =$ `GL (Fin 2) (AdeleRing R K)`. Two structural facts are recorded: `center_eq_range_scalar` identifies $Z(G)$ with the range of the scalar homomorphism $\mathbb{A}_K^\times \to G$, $w \mapsto w\cdot 1$ (quoting Mathlib's computation of the centre of $\mathrm{GL}_n$ over a commutative ring), and `scalar_injective` shows that homomorphism is injective, by reading off the $(0,0)$ entry. `AdelicPGL2 R K` is defined as an abbreviation for the quotient group $G / Z(G)$, i.e. $\mathrm{PGL}_2(\mathbb{A}_K)$ realised as a central quotient, not via any projective-space model.
--
--   Three transfer lemmas concern the projection $\pi =$ `QuotientGroup.mk`. For an arbitrary $\sigma$-algebra on the quotient and a measure $\mu$ positive on nonempty open sets, `measure_image_mk_pos` gives $\mu(\pi(D)) > 0$ as soon as $D$ contains a nonempty open subset of $G$ (using that $\pi$ is an open map); `measure_image_mk_lt_top` gives $\mu(\pi(C)) < \infty$ for $C$ compact when $\mu$ is finite on compacts; and `image_mk_subset_of_subset_mul_center` is the purely set-theoretic statement $D \subseteq C\cdot Z(G) \Rightarrow \pi(D) \subseteq \pi(C)$.
--
--   In the number-field case ($R$ finite free over $\mathbb{Z}$, $K$ a number field) the centre is shown closed, as the intersection over $g \in G$ of the closed sets $\{z : gz = zg\}$, whence $\mathrm{PGL}_2(\mathbb{A}_K)$ is Hausdorff, locally compact and a topological group. `pglBorel` is the Borel $\sigma$-algebra (a definition rather than a global instance), with `borelSpace_pglBorel` the corresponding `BorelSpace` witness, and `adelicPGLHaar` is Mathlib's Haar measure for these data, `isHaarMeasure_adelicPGLHaar` asserting that it is a Haar measure; no normalisation is pinned. The last two results specialise the transfers to `adelicPGLHaar`: positivity of the image of any set with nonempty interior, and finiteness of the image of any set contained in $C \cdot Z(G)$ with $C$ compact. Nothing is asserted about unimodularity, second countability, or a quotient (Weil) measure formula relating Haar measures on $G$ and on the quotient.
--
--   **Relation to Mathlib.** The centre computation is Mathlib's `Matrix.GeneralLinearGroup.center_eq_range_scalar`, cited rather than reproved; the quotient topology, Hausdorffness and local compactness of $G/Z(G)$ come from Mathlib's quotient-group instances, and `adelicPGLHaar` is Mathlib's `Measure.haar` for the Borel structure fixed by `pglBorel`.
--
--   **Where it is used.** These declarations provide the measure-theoretic setting in which adelic volume statements for $\mathrm{GL}_2$ are reduced modulo the centre, the usual preliminary to working with automorphic forms on $\mathrm{GL}_2(\mathbb{A}_K)$ on the analytic side of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_AdelicCentre.lean

import Definitions.Def_NumberField_AdelicHaar
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField MeasureTheory
open scoped Pointwise

noncomputable section

namespace NumberField.AdelicCentre

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem center_eq_range_scalar :
    Subgroup.center (GL (Fin 2) (AdeleRing R K))
      = (Matrix.GeneralLinearGroup.scalar (Fin 2) : (AdeleRing R K)ˣ →* _).range :=
  Matrix.GeneralLinearGroup.center_eq_range_scalar

theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : (AdeleRing R K)ˣ →* _) :=
  fun a b h => by
    have := congrArg (fun g : GL (Fin 2) (AdeleRing R K) => (g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0) h
    exact Units.ext (by simpa using this)

abbrev AdelicPGL2 : Type _ :=
  GL (Fin 2) (AdeleRing R K) ⧸ Subgroup.center (GL (Fin 2) (AdeleRing R K))

theorem measure_image_mk_pos {m : MeasurableSpace (AdelicPGL2 R K)} (μ : Measure (AdelicPGL2 R K))
    [μ.IsOpenPosMeasure] {D : Set (GL (Fin 2) (AdeleRing R K))}
    (h : ∃ U : Set (GL (Fin 2) (AdeleRing R K)), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    0 < μ ((QuotientGroup.mk : GL (Fin 2) (AdeleRing R K) → AdelicPGL2 R K) '' D) := by
  obtain ⟨U, hU, hne, hsub⟩ := h
  exact ((QuotientGroup.isOpenMap_coe U hU).measure_pos μ (hne.image _)).trans_le
    (measure_mono (Set.image_mono hsub))

theorem measure_image_mk_lt_top {m : MeasurableSpace (AdelicPGL2 R K)} (μ : Measure (AdelicPGL2 R K))
    [IsFiniteMeasureOnCompacts μ] {C : Set (GL (Fin 2) (AdeleRing R K))} (hC : IsCompact C) :
    μ ((QuotientGroup.mk : GL (Fin 2) (AdeleRing R K) → AdelicPGL2 R K) '' C) < ⊤ :=
  (hC.image QuotientGroup.continuous_mk).measure_lt_top

theorem image_mk_subset_of_subset_mul_center {D C : Set (GL (Fin 2) (AdeleRing R K))}
    (h : D ⊆ C * ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))) :
    (QuotientGroup.mk : _ → AdelicPGL2 R K) '' D ⊆ (QuotientGroup.mk : _ → AdelicPGL2 R K) '' C := by
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨c, hc, z, hz, rfl⟩ := h hd
  refine ⟨c, hc, ?_⟩
  rw [QuotientGroup.eq]
  simpa using hz

@[reducible] def pglBorel : MeasurableSpace (AdelicPGL2 R K) := borel _

theorem borelSpace_pglBorel : @BorelSpace (AdelicPGL2 R K) _ (pglBorel R K) :=
  @BorelSpace.mk _ _ (pglBorel R K) rfl

section NumberFieldCase

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]

instance isClosed_center :
    IsClosed ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K)))) := by
  have : ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))
      = ⋂ g : GL (Fin 2) (AdeleRing R K), {z | g * z = z * g} := by
    ext z
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun g =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

instance t2Space_adelicPGL2 : T2Space (AdelicPGL2 R K) := inferInstance

instance locallyCompactSpace_adelicPGL2 : LocallyCompactSpace (AdelicPGL2 R K) := inferInstance

instance isTopologicalGroup_adelicPGL2 : IsTopologicalGroup (AdelicPGL2 R K) := inferInstance

def adelicPGLHaar : @Measure (AdelicPGL2 R K) (pglBorel R K) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  exact Measure.haar

theorem isHaarMeasure_adelicPGLHaar :
    @Measure.IsHaarMeasure (AdelicPGL2 R K) _ _ (pglBorel R K) (adelicPGLHaar R K) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  exact Measure.isHaarMeasure_haarMeasure _

theorem adelicPGLHaar_image_pos {D : Set (GL (Fin 2) (AdeleRing R K))}
    (h : ∃ U : Set (GL (Fin 2) (AdeleRing R K)), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    0 < adelicPGLHaar R K ((QuotientGroup.mk : _ → AdelicPGL2 R K) '' D) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  haveI := isHaarMeasure_adelicPGLHaar R K
  exact measure_image_mk_pos R K _ h

theorem adelicPGLHaar_image_lt_top_of_subset {D C : Set (GL (Fin 2) (AdeleRing R K))} (hC : IsCompact C)
    (h : D ⊆ C * ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))) :
    adelicPGLHaar R K ((QuotientGroup.mk : _ → AdelicPGL2 R K) '' D) < ⊤ := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  haveI := isHaarMeasure_adelicPGLHaar R K
  exact lt_of_le_of_lt (measure_mono (image_mk_subset_of_subset_mul_center R K h))
    (measure_image_mk_lt_top R K _ hC)

end NumberFieldCase

end NumberField.AdelicCentre

end


