-- Prove2me | Definitions.Def_SP4RelHomology
-- name    : SP4RelHomology
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-12T22:18:52.481983+00:00
-- url     : https://prove2.me/theorems/9976fbe8-9928-4ddc-837c-f20b6e5ed0b0
-- title:
--   Relative singular homology $H_k(M,V;\mathbb Z)$, the map $j_*$ and the connecting homomorphism $\partial$
-- statement:
--   Let $\iota\colon V\to M$ be a continuous map between topological spaces (in universe zero), thought of as the inclusion of a subspace. The **relative singular chain complex** of the pair is the quotient
--
--   $$
--   C_\bullet(M,V;\mathbb Z)\;:=\;C_\bullet(M;\mathbb Z)\big/\iota_\#C_\bullet(V;\mathbb Z),
--   $$
--
--   realized as the cokernel of the chain map $\iota_\#$ in the abelian category of chain complexes of $\mathbb Z$-modules, and the **relative singular homology** $H_k(M,V;\mathbb Z)$ is its $k$-th homology (Hatcher, §2.1, p. 115). The quotient map $C_\bullet(M)\to C_\bullet(M,V)$ induces $j_*\colon H_k(M;\mathbb Z)\to H_k(M,V;\mathbb Z)$. When $\iota$ is injective, $0\to C_\bullet(V)\to C_\bullet(M)\to C_\bullet(M,V)\to0$ is a short exact sequence of chain complexes, and the **connecting homomorphism**
--
--   $$
--   \partial\colon H_{k+1}(M,V;\mathbb Z)\longrightarrow H_k(V;\mathbb Z)
--   $$
--
--   is the one furnished by the snake lemma (Hatcher, §2.1, p. 116). The file also records the three vanishing compositions $j_*\circ\iota_*=0$, $\partial\circ j_*=0$ and $\iota_*\circ\partial=0$, which are the trivial half of the exactness of the long exact sequence of the pair.
--
--   **Formalization Note** `SP4Homology.Chains X` is Mathlib's singular chain complex with coefficients in the $\mathbb Z$-module $\mathbb Z$; `SP4Homology.RelChains ι` is `cokernel (chainsMap ι)`; `SP4Homology.Hrel k ι` is its homology in degree `k`; `SP4Homology.toRel k ι` is `homologyMap (cokernel.π _) k`; `SP4Homology.relShortComplex_shortExact ι hι` proves short exactness for injective `ι` using that Mathlib's singular chain complex functor preserves monomorphisms; and `SP4Homology.relδ k ι hι` is Mathlib's connecting homomorphism `ShortComplex.ShortExact.δ` for the degrees `k + 1` and `k`. The degree-`k` connecting map is indexed so that its source is `H_{k+1}(M, V)`.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1, pp. 115–116: definition of the relative chain groups Cₙ(X, A) = Cₙ(X)/Cₙ(A), the relative homology groups Hₙ(X, A), and the boundary map ∂ : Hₙ(C) → Hₙ₋₁(A) of a short exact sequence of chain complexes. Mathlib: `CategoryTheory.ShortComplex.ShortExact.δ` (Mathlib/Algebra/Homology/HomologySequence.lean).

import Definitions.Def_SP4HomologyMap
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Topology.Category.TopCat.EpiMono

set_option autoImplicit false

open CategoryTheory AlgebraicTopology Limits

namespace SP4Homology

/-- The integral singular chain complex `C_•(X; ℤ)` of a space `X` (Hatcher, §2.1, p. 108). -/
noncomputable abbrev Chains (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

/-- The chain map `f_# : C_•(X) → C_•(Y)` induced by a continuous map. -/
noncomputable abbrev chainsMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Chains X ⟶ Chains Y :=
  ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

variable {V M : Type} [TopologicalSpace V] [TopologicalSpace M]

/-- **Relative singular chains** `C_•(M, V; ℤ) := C_•(M)/C_•(V)` of the pair given by a map
`ι : V → M` (intended to be the inclusion of a subspace), as the cokernel of `ι_#`
(Hatcher, §2.1, p. 115). -/
noncomputable def RelChains (ι : C(V, M)) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (chainsMap ι)

/-- **Relative singular homology** `H_k(M, V; ℤ)` (Hatcher, §2.1, p. 115). -/
noncomputable def Hrel (k : ℕ) (ι : C(V, M)) : ModuleCat.{0} ℤ := (RelChains ι).homology k

/-- The map `j_* : H_k(M) → H_k(M, V)` induced by the quotient `C_•(M) → C_•(M, V)`. -/
noncomputable def toRel (k : ℕ) (ι : C(V, M)) : H k M ⟶ Hrel k ι :=
  HomologicalComplex.homologyMap (cokernel.π (chainsMap ι)) k

/-- The short complex of chain complexes `C_•(V) → C_•(M) → C_•(M, V)`. -/
noncomputable def relShortComplex (ι : C(V, M)) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (chainsMap ι) (cokernel.π (chainsMap ι)) (cokernel.condition _)

/-- For an injective `ι`, `0 → C_•(V) → C_•(M) → C_•(M, V) → 0` is short exact. -/
theorem relShortComplex_shortExact (ι : C(V, M)) (hι : Function.Injective ι) :
    (relShortComplex ι).ShortExact := by
  have hmono : Mono (TopCat.ofHom ι) := (TopCat.mono_iff_injective _).mpr hι
  have : Mono (chainsMap ι) :=
    Functor.map_mono ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)) _
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
          mono_f := this
          epi_g := by dsimp [relShortComplex]; infer_instance }

/-- The **connecting homomorphism** `∂ : H_{k+1}(M, V) → H_k(V)` of the pair, for an injective
`ι` (Hatcher, §2.1, p. 116). -/
noncomputable def relδ (k : ℕ) (ι : C(V, M)) (hι : Function.Injective ι) :
    Hrel (k + 1) ι ⟶ H k V :=
  (relShortComplex_shortExact ι hι).δ (k + 1) k rfl

theorem map_toRel (k : ℕ) (ι : C(V, M)) : map k ι ≫ toRel k ι = 0 := by
  show HomologicalComplex.homologyMap _ k ≫ HomologicalComplex.homologyMap _ k = 0
  rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
    HomologicalComplex.homologyMap_zero]
  rfl

theorem toRel_relδ (k : ℕ) (ι : C(V, M)) (hι : Function.Injective ι) :
    toRel (k + 1) ι ≫ relδ k ι hι = 0 :=
  (relShortComplex_shortExact ι hι).comp_δ (k + 1) k rfl

theorem relδ_map (k : ℕ) (ι : C(V, M)) (hι : Function.Injective ι) :
    relδ k ι hι ≫ map k ι = 0 :=
  (relShortComplex_shortExact ι hι).δ_comp (k + 1) k rfl

end SP4Homology


