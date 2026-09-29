-- Prove2me | Definitions.Def_LocalLanglands_IntegralSubgroupOpen
-- name    : LocalLanglands_IntegralSubgroupOpen
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/91ebb95c-28cd-5b7e-a001-00031c623fb6
-- title:
--   Entrywise criterion and openness of GL₂(ℤ_p) in GL₂(ℚ_p)
-- statement:
--   For a commutative ring $R$, a field $K$ and an algebra structure $R \to K$, the subgroup $\mathrm{integralSubgroup}\ R\ K \le \mathrm{GL}_2(K)$ is the image of $\mathrm{GL}_2(R)$ under the group homomorphism induced by $\mathrm{algebraMap}\colon R \to K$ applied entrywise. Three results about it are recorded here. First, [`LocalGL2.exists_entry_eq_of_mem_integralSubgroup`](../def/LocalLanglands_IntegralSubgroupOpen.html#L10): if $x \in \mathrm{integralSubgroup}\ R\ K$ then for all $i,j \in \{0,1\}$ there is $r \in R$ with $\mathrm{algebraMap}(r)$ equal to the $(i,j)$ entry of $x$. Second, [`FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem`](../def/LocalLanglands_IntegralSubgroupOpen.html#L21): assuming $\mathrm{algebraMap}\colon R \to K$ is injective, an element $g \in \mathrm{GL}_2(K)$ lies in $\mathrm{integralSubgroup}\ R\ K$ if and only if every entry of the matrix of $g$ and every entry of the matrix of $g^{-1}$ lies in the range of $\mathrm{algebraMap}$; the nontrivial direction assembles the two entrywise preimages into matrices over $R$ that are mutually inverse, injectivity of the entrywise map being what forces the two product identities over $R$.
--
--   Third, in the $p$-adic case: [`FLT.SpectralSide.range_algebraMap_padicInt`](../def/LocalLanglands_IntegralSubgroupOpen.html#L71) identifies the range of $\mathrm{algebraMap}\colon \mathbb{Z}_p \to \mathbb{Q}_p$ with the range of the coercion $\mathbb{Z}_p \to \mathbb{Q}_p$, and [`FLT.SpectralSide.isOpen_coe_integralSubgroup_padic`](../def/LocalLanglands_IntegralSubgroupOpen.html#L80) states that for a prime $p$ the underlying set of $\mathrm{integralSubgroup}\ \mathbb{Z}_p\ \mathbb{Q}_p$ is open in $\mathrm{GL}_2(\mathbb{Q}_p)$. The proof rewrites that set, via the entrywise criterion, as a finite intersection of preimages of the open set $\mathbb{Z}_p \subseteq \mathbb{Q}_p$ under the eight continuous maps $g \mapsto g_{ij}$ and $g \mapsto (g^{-1})_{ij}$ on the unit group.
--
--   **Relation to Mathlib.** The subgroup $\mathrm{integralSubgroup}$ is the project's own, defined as the range of Mathlib's `Matrix.GeneralLinearGroup.map` along `algebraMap`; the topological input (openness of the image of $\mathbb{Z}_p$ in $\mathbb{Q}_p$, and continuity of the entries of a unit and of its inverse) is Mathlib's.
--
--   **Where it is used.** The group $\mathrm{GL}_2(\mathbb{Z}_p) \le \mathrm{GL}_2(\mathbb{Q}_p)$ serves as the level subgroup for the local Hecke pair at $p$, whose double cosets give the local Hecke algebra and the operators $T_p$; openness of this subgroup is what makes the associated coset decompositions and Hecke-operator constructions available at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalLanglands_IntegralSubgroupOpen.lean

import Mathlib
import Definitions.Def_LocalLanglands_LocalHeckeInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix

namespace LocalGL2

lemma exists_entry_eq_of_mem_integralSubgroup {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K] {x : GL (Fin 2) K}
    (hx : x ∈ integralSubgroup R K) (i j : Fin 2) :
    ∃ r : R, algebraMap R K r = (x : Matrix (Fin 2) (Fin 2) K) i j := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(y : Matrix (Fin 2) (Fin 2) R) i j, rfl⟩

end LocalGL2

namespace FLT.SpectralSide

theorem mem_integralSubgroup_iff_entries_mem {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    (g : GL (Fin 2) K) :
    g ∈ LocalGL2.integralSubgroup R K
      ↔ (∀ i j, (g : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
        ∧ (∀ i j, ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
            ∈ Set.range (algebraMap R K)) := by
  constructor
  · intro hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup hg i j
      exact ⟨r, hr⟩
    · obtain ⟨r, hr⟩ :=
        LocalGL2.exists_entry_eq_of_mem_integralSubgroup (inv_mem hg) i j
      exact ⟨r, hr⟩
  · rintro ⟨hg, hginv⟩
    set A : Matrix (Fin 2) (Fin 2) R := fun i j => (hg i j).choose with hA
    set B : Matrix (Fin 2) (Fin 2) R := fun i j => (hginv i j).choose with hB
    have hAspec : ∀ i j, algebraMap R K (A i j) = (g : Matrix (Fin 2) (Fin 2) K) i j :=
      fun i j => (hg i j).choose_spec
    have hBspec : ∀ i j,
        algebraMap R K (B i j) = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j :=
      fun i j => (hginv i j).choose_spec
    have hmapA : (A.map (algebraMap R K)) = (g : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hAspec i j
    have hmapB : (B.map (algebraMap R K))
        = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hBspec i j
    have hmatinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) R =>
        M.map (algebraMap R K) := fun M M' hMM' => by
      ext i j
      apply hinj
      have := congrFun (congrFun hMM' i) j
      simpa [Matrix.map_apply] using this
    have hAB : A * B = 1 := by
      apply hmatinj
      simp only [Matrix.map_mul, Matrix.map_one (algebraMap R K) (map_zero _) (map_one _),
        hmapA, hmapB]
      exact (Units.mul_inv g)
    have hBA : B * A = 1 := by
      apply hmatinj
      simp only [Matrix.map_mul, Matrix.map_one (algebraMap R K) (map_zero _) (map_one _),
        hmapA, hmapB]
      exact (Units.inv_mul g)
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    apply Units.ext
    exact hmapA

theorem range_algebraMap_padicInt (p : ℕ) [Fact p.Prime] :
    Set.range (algebraMap ℤ_[p] ℚ_[p]) = Set.range ((↑) : ℤ_[p] → ℚ_[p]) := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, (PadicInt.algebraMap_apply r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, PadicInt.algebraMap_apply r⟩

theorem isOpen_coe_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    IsOpen ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] : Set (GL (Fin 2) ℚ_[p]))) := by
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := fun a b hab => by
    have ha := PadicInt.algebraMap_apply (p := p) a
    have hb := PadicInt.algebraMap_apply (p := p) b
    rw [ha, hb] at hab
    exact Subtype.coe_injective hab
  have hOopen : IsOpen (Set.range (algebraMap ℤ_[p] ℚ_[p])) := by
    rw [range_algebraMap_padicInt p]
    exact PadicInt.isOpenEmbedding_coe.isOpen_range
  have hchar : (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] : Set (GL (Fin 2) ℚ_[p]))
      = (⋂ i, ⋂ j, {g : GL (Fin 2) ℚ_[p] |
            (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j ∈ Set.range (algebraMap ℤ_[p] ℚ_[p])})
        ∩ (⋂ i, ⋂ j, {g : GL (Fin 2) ℚ_[p] |
            ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j
              ∈ Set.range (algebraMap ℤ_[p] ℚ_[p])}) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_integralSubgroup_iff_entries_mem hinj g
  rw [hchar]
  refine IsOpen.inter ?_ ?_
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hOopen.preimage (Units.continuous_val.matrix_elem i j)
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hOopen.preimage (Units.continuous_coe_inv.matrix_elem i j)

end FLT.SpectralSide


