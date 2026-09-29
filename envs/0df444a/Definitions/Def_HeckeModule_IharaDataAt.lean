-- Prove2me | Definitions.Def_HeckeModule_IharaDataAt
-- name    : HeckeModule_IharaDataAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/91409b1f-5752-5013-8a96-f358c58e1df7
-- title:
--   Ihara data at a pair of points; corner rungs
-- statement:
--   The setting is a pair of commutative $\mathcal{O}$-algebras $T$, $T'$ acting on $\mathcal{O}$-modules $M$, $M'$ (compatibly with the $\mathcal{O}$-actions), each equipped with a `LevelPairing`: an $\mathcal{O}$-bilinear form $B$ on the module which is self-adjoint for the algebra action ($B(tm,n)=B(m,tn)$) and perfect in the sense that $m \mapsto B(m,\cdot)$ is bijective. A `RungDatum` between these consists of an $\mathcal{O}$-algebra map $\mathrm{res} : T' \to T$, $\mathcal{O}$-linear maps $i : M \to M'$ and $j : M' \to M$ adjoint for the two pairings ($B(j m', m) = B'(m', i m)$), and an element $\Delta \in T$ with $j \circ i = \Delta \cdot \mathrm{id}_M$.
--
--   The predicate `IsIharaDataAt D πT πT'`, for such a rung datum $D$ and $\mathcal{O}$-algebra maps $\pi_T : T \to \mathcal{O}$, $\pi_{T'} : T' \to \mathcal{O}$, is a one-field structure asserting a single equality of $\mathcal{O}$-submodules of $M'$: the preimage under $D.j$ of $(\ker \pi_T)\, M \subseteq M$ equals $(\ker \pi_{T'})\, M' \subseteq M'$. Equivalently, $D.j$ induces an injection $M'/(\ker \pi_{T'})M' \hookrightarrow M/(\ker \pi_T)M$ on these cotorsion quotients, together with the containment $D.j\big((\ker \pi_{T'})M'\big) \subseteq (\ker \pi_T)M$.
--
--   The second part of the module constructs rungs at corner slots. Given idempotent splittings $S$ of $\mathbb{T}$ and $S'$ of $\mathbb{T}'$ (complete orthogonal idempotents $e_i$ indexed by the maximal ideals $\mathfrak{m}_i$, with $e_i \in \mathfrak{m}_j$ exactly when $i \neq j$), indices $i_0$, $i_0'$, level pairings on the corner rings $e_{i_0}\mathbb{T}e_{i_0}$ acting on the corner submodules $e_{i_0} V$, a `LegDatum` $L$ of $n$ legs (maps $i_k : e_{i_0}V \to e_{i_0'}V'$ and $j_k$ back, pairwise adjoint, with $j_k \circ i_{k'} = \mathrm{table}(k,k') \cdot \mathrm{id}$), a coefficient vector $c : \mathrm{Fin}\,n \to e_{i_0}\mathbb{T}e_{i_0}$ and a restriction map $\mathrm{res}$, `cornerRung` is the rung datum assembled from the legs. Four lemmas record its components: the restriction map is $\mathrm{res}$, the raising map is $\sum_k i_k \circ (c_k \cdot)$, the lowering map is $\sum_k (c_k \cdot) \circ j_k$, and $\Delta = \sum_{k,k'} c_k\,\mathrm{table}(k,k')\,c_{k'}$.
--
--   **Relation to Mathlib.** Mathlib has no notion of level pairing, rung datum or Ihara data; these are the project's own. The corner constructions build on Mathlib's `CompleteOrthogonalIdempotents` and the corner ring of an idempotent, and the submodule operations used (`Submodule.comap`, `restrictScalars`, ideal-times-submodule) are Mathlib's.
--
--   **Where it is used.** The cotorsion equality packaged by `IsIharaDataAt` is the form of Ihara's lemma used to compare Hecke modules at two levels: it is cited where congruence-module and $\eta$-invariant comparisons between a held and a raised level are needed in the modularity-lifting argument. The corner-rung construction supplies such rung data at the local factors cut out by an idempotent splitting of a Hecke algebra, assembling the raising and lowering maps from a finite family of degeneracy-type legs with coefficients in the corner ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HeckeModule_IharaDataAt.lean

import Definitions.Def_HeckeModule_IharaRungDatum
import Definitions.Def_IharaLemma_IdempotentSplitting

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace IharaTower

variable {𝒪 : Type} [CommRing 𝒪]
  {T : Type} [CommRing T] [Algebra 𝒪 T]
  {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}

structure IsIharaDataAt (D : RungDatum T T' M M' P P')
    (πT : T →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪) : Prop where
  cotorsion_comap_eq :
    Submodule.comap D.j (((RingHom.ker πT) • (⊤ : Submodule T M)).restrictScalars 𝒪) =
      ((RingHom.ker πT') • (⊤ : Submodule T' M')).restrictScalars 𝒪

section CornerRung

open IharaLemma

variable {𝒪 : Type} [CommRing 𝒪]
  {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup V'] [Module 𝒪 V']
  {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
  [Module 𝕋 V] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋 V] [IsScalarTower 𝒪 𝕋' V']
  (S : IdempotentSplitting 𝕋) (S' : IdempotentSplitting 𝕋') (i₀ : Fin S.n) (i₀' : Fin S'.n)
  (P : LevelPairing (𝒪 := 𝒪) (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀)))
  (P' : LevelPairing (𝒪 := 𝒪) (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀')))
  {n : ℕ}
  (L : RungAssembly.LegDatum (T := S.CornerRing i₀) (T' := S'.CornerRing i₀')
    (M := ↥(cornerSubmodule (M := V) (S.e i₀)))
    (M' := ↥(cornerSubmodule (M := V') (S'.e i₀')))
    (𝒪 := 𝒪) P P' n)
  (c : Fin n → S.CornerRing i₀) (res : S'.CornerRing i₀' →ₐ[𝒪] S.CornerRing i₀)

noncomputable def cornerRung :
    RungDatum (𝒪 := 𝒪) (S.CornerRing i₀) (S'.CornerRing i₀')
      ↥(cornerSubmodule (M := V) (S.e i₀)) ↥(cornerSubmodule (M := V') (S'.e i₀')) P P' :=
  RungAssembly.rungDatumOfLegs L c res

theorem cornerRung_res : (cornerRung S S' i₀ i₀' P P' L c res).res = res := rfl

theorem cornerRung_i :
    (cornerRung S S' i₀ i₀' P P' L c res).i = RungAssembly.iComb L c := rfl

theorem cornerRung_j :
    (cornerRung S S' i₀ i₀' P P' L c res).j = RungAssembly.jComb L c := rfl

theorem cornerRung_delta :
    (cornerRung S S' i₀ i₀' P P' L c res).Δ = RungAssembly.deltaComb L c := rfl

end CornerRung

end IharaTower


