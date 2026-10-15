-- Prove2me | Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
-- name    : OAI_Algebra_BogomolovPop_Foundations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:19:35.89456+00:00
-- url     : https://prove2.me/theorems/a0b3d362-f93a-4895-89bc-604b8df8c834
-- title:
--   Profinite Galois groups, commutator brackets and $\mathbb{Z}_\ell$-module structures on abelian pro-$\ell$ groups
-- statement:
--   This file develops the topological group theory needed to treat absolute Galois groups, their maximal pro-$\ell$ quotients and the associated abelian and two-step nilpotent quotients as profinite groups, and it equips abelian pro-$\ell$ groups with their natural $\mathbb{Z}_\ell$-module structure.
--
--   Notation (from the base definitions). For a field $F$, $\overline{F}$ is a fixed algebraic closure, $F^{\mathrm{perf}}\subseteq\overline{F}$ the perfect closure of $F$ inside it, and $G_F=\operatorname{Aut}_F(\overline{F})$ the absolute Galois group with the Krull topology. A group is an *$\ell$-group* if every element $g$ satisfies $g^{\ell^j}=1$ for some $j\ge 0$. For a topological group $G$, $N_\ell(G)$ is the intersection of all open normal subgroups $H$ such that $G/H$ is an $\ell$-group, $\overline{[G,G]}$ is the closed commutator subgroup, and $\overline{\gamma}_3(G)$ is the closure of $[\overline{[G,G]},G]$. For a field $F$ put $\mathcal{G}_F=G_F/N_\ell(G_F)$ (the maximal pro-$\ell$ quotient), $\Pi^a_F=\mathcal{G}_F/\overline{[\mathcal{G}_F,\mathcal{G}_F]}$, $\Pi^c_F=\mathcal{G}_F/\overline{\gamma}_3(\mathcal{G}_F)$ and $\Delta_F=\ker(\Pi^c_F\to\Pi^a_F)$; for $x,y\in\Pi^a_F$ the bracket $[x,y]\in\Delta_F$ is the image in $\Pi^c_F$ of $a^{-1}b^{-1}ab$, where $a,b\in\mathcal{G}_F$ are fixed lifts of $x,y$.
--
--   1. **Commutators modulo $\overline{\gamma}_3$.** In any topological group $G$, the image in $G/\overline{\gamma}_3(G)$ of an element of $\overline{[G,G]}$ commutes with the image of every element of $G$. Consequently, if $a\equiv a'$ and $b\equiv b'$ modulo $\overline{[G,G]}$, then
--   $$aba^{-1}b^{-1}\equiv a'b'(a')^{-1}(b')^{-1}\quad\text{and}\quad a^{-1}b^{-1}ab\equiv (a')^{-1}(b')^{-1}a'b' \pmod{\overline{\gamma}_3(G)}.$$
--   In particular $[x,y]$ equals the image of $a^{-1}b^{-1}ab$ for *any* lifts $a,b\in\mathcal{G}_F$ of $x,y\in\Pi^a_F$.
--   2. **Absolute Galois groups are profinite.** For every field $F$, $G_F$ is compact, Hausdorff and non-archimedean (its open subgroups form a neighbourhood basis of the identity). The file also shows that for fields $F\subseteq P\subseteq A$ with $A/P$ algebraic, the restriction map $\operatorname{Aut}_P(A)\to\operatorname{Aut}_F(A)$ is continuous for the Krull topologies, and that it is surjective when $P/F$ is purely inseparable; this is applied to the tower $F\subseteq F^{\mathrm{perf}}\subseteq\overline{F}$.
--   3. **Quotients.** If $G$ is a compact, totally disconnected topological group and $N$ is a normal subgroup, then $G/N$ is non-archimedean; moreover $N_\ell(G)$ is closed in every topological group $G$. Hence $\mathcal{G}_F$, $\Pi^a_F$ and $\Pi^c_F$ are Hausdorff and totally disconnected.
--   4. **Finite $\ell$-quotients.** Let $\mathcal{E}_\ell(G)$ be the set of open normal subgroups $H$ of $G$ with $G/H$ an $\ell$-group. The evaluation map
--   $$G/N_\ell(G)\longrightarrow\prod_{H\in\mathcal{E}_\ell(G)}G/H$$
--   is an injective continuous homomorphism, and it is a closed embedding when $G$ is a compact topological group. For such $G$, every $x\in G/N_\ell(G)$ satisfies $x^{\ell^n}\to 1$ as $n\to\infty$, and whenever $G/N_\ell(G)\to A\to Q$ are continuous surjective homomorphisms onto groups $A$, $Q$ with $Q$ discrete, $Q$ is an $\ell$-group.
--   5. **$\mathbb{Z}_\ell$-modules: the finite case.** Let $\ell$ be prime. The reduction maps $\mathbb{Z}_\ell\to\mathbb{Z}/\ell^n\mathbb{Z}$ are continuous. A finite abelian group $A$ which is an $\ell$-group satisfies $\ell^n A=0$ for some $n$, and becomes a $\mathbb{Z}_\ell$-module through $\mathbb{Z}_\ell\to\mathbb{Z}/\ell^n\mathbb{Z}$; for the discrete topology on $A$ this scalar multiplication is continuous.
--   6. **$\mathbb{Z}_\ell$-modules: the profinite case.** Let $\ell$ be prime and let $A$ be an abelian topological group that is compact, Hausdorff and non-archimedean, such that $A/H$ is an $\ell$-group for every open subgroup $H$. Each $A/H$ is finite and discrete, hence a $\mathbb{Z}_\ell$-module as in item 5, and the evaluation map
--   $$\lambda:A\longrightarrow\prod_{H\le A\ \text{open}}A/H$$
--   is a closed embedding whose image is a $\mathbb{Z}_\ell$-submodule. Transporting the module structure along $\lambda$ gives the canonical $\mathbb{Z}_\ell$-module structure on $A$: $c\cdot x$ is the unique element of $A$ whose image in each $A/H$ is $c$ times the image of $x$. With this structure $\lambda$ is $\mathbb{Z}_\ell$-linear and the scalar multiplication $\mathbb{Z}_\ell\times A\to A$ is continuous.
--
--   These results make the Galois-theoretic groups $\mathcal{G}_F$, $\Pi^a_F$, $\Pi^c_F$ and $\Delta_F$ usable as profinite groups. Item 6 is the source of the $\mathbb{Z}_\ell$-module structures on $\Pi^a_F$ and $\Delta_F$, which give a meaning to raising their elements to $\ell$-adic powers, and item 1 makes the commutator bracket $\Pi^a_F\times\Pi^a_F\to\Delta_F$ independent of the chosen lifts.
--
--   **Formalization Note** $G_F$ is `Field.absoluteGaloisGroup F`, the group of `F`-algebra automorphisms of Mathlib's `AlgebraicClosure F`; $N_\ell$, $\mathcal{G}_F$, $\Pi^a_F$, $\Pi^c_F$, $\Delta_F$, $\overline{\gamma}_3$ and the bracket are `proEllKernel`, `ProEll`, `PiA`, `PiC`, `Delta`, `closedGammaThree` and `bracket` of the base definitions (where the lifts are chosen with `Quotient.out`). The $\ell$-group condition is Mathlib's `IsPGroup ell`, applied to `Multiplicative A` for an additive group `A`; $\ell$ is an arbitrary natural number except where `Fact ell.Prime` is assumed (items 5 and 6). $\mathcal{E}_\ell(G)$ is `EllQuotients`, the evaluation maps are `proEllEval` and `levelEval` (into `AllLevels A`), the hypothesis of item 6 is `AllLevelsEll ell A`, supplied as a `Fact`, and the module structure is `abelianEllModule`, transported from the submodule `levelImage` along `levelImageEquiv`. In item 5 (`finiteEllModule`) the exponent $n$ is chosen with `Classical.choose`. The remaining declarations are the instances recording compactness, the Hausdorff property, non-archimedean-ness and total disconnectedness of $G_F$, `ProEll`, `PiA` and `PiC`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/BogomolovPop/Foundations.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/BogomolovPop/Foundations.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BogomolovPopInjectivity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BogomolovPopInjectivity

namespace OAI

/-! Literal Galois objects, quotient topology and continuous ell-adic actions. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop

end BogomolovPop

namespace BogomolovPop
open scoped commutatorElement

theorem closedCommutator_image_commute {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {z : G}
    (hz : z ∈ (commutator G).topologicalClosure) (g : G) :
    Commute (QuotientGroup.mk' (closedGammaThree G) z)
      (QuotientGroup.mk' (closedGammaThree G) g) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.le_topologicalClosure _
    (Subgroup.commutator_mem_commutator hz (Subgroup.mem_top g))

theorem quotient_commutator_independent {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {a a' b b' : G}
    (ha : QuotientGroup.mk' (commutator G).topologicalClosure a =
      QuotientGroup.mk' (commutator G).topologicalClosure a')
    (hb : QuotientGroup.mk' (commutator G).topologicalClosure b =
      QuotientGroup.mk' (commutator G).topologicalClosure b') :
    QuotientGroup.mk' (closedGammaThree G) ⁅a, b⁆ =
      QuotientGroup.mk' (closedGammaThree G) ⁅a', b'⁆ := by
  let q := QuotientGroup.mk' (closedGammaThree G)
  have haz : a⁻¹ * a' ∈ (commutator G).topologicalClosure :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact ha)
  have hbz : b⁻¹ * b' ∈ (commutator G).topologicalClosure :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact hb)
  have hea : q a' = q a * q (a⁻¹ * a') := by rw [← map_mul]; simp
  have heb : q b' = q b * q (b⁻¹ * b') := by rw [← map_mul]; simp
  change q ⁅a, b⁆ = q ⁅a', b'⁆
  rw [map_commutatorElement, map_commutatorElement, hea, heb]
  have hza : Commute (q (a⁻¹ * a')) (q b * q (b⁻¹ * b')) := by
    rw [← map_mul]
    exact closedCommutator_image_commute haz _
  rw [commutatorElement_mul_left_eq_conj_mul, hza.commutator_eq]
  simp only [mul_one, mul_inv_cancel, one_mul]
  rw [commutatorElement_mul_right_eq_mul_conj,
    (closedCommutator_image_commute hbz a).symm.commutator_eq]
  simp [mul_assoc]

end BogomolovPop

namespace BogomolovPop
open scoped commutatorElement

theorem sourceCommutator_independent {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {a a' b b' : G}
    (ha : QuotientGroup.mk' (commutator G).topologicalClosure a =
      QuotientGroup.mk' (commutator G).topologicalClosure a')
    (hb : QuotientGroup.mk' (commutator G).topologicalClosure b =
      QuotientGroup.mk' (commutator G).topologicalClosure b') :
    QuotientGroup.mk' (closedGammaThree G) (sourceCommutator a b) =
      QuotientGroup.mk' (closedGammaThree G) (sourceCommutator a' b') := by
  have ha' : QuotientGroup.mk' (commutator G).topologicalClosure a⁻¹ =
      QuotientGroup.mk' (commutator G).topologicalClosure a'⁻¹ := by
    simpa only [map_inv] using congrArg Inv.inv ha
  have hb' : QuotientGroup.mk' (commutator G).topologicalClosure b⁻¹ =
      QuotientGroup.mk' (commutator G).topologicalClosure b'⁻¹ := by
    simpa only [map_inv] using congrArg Inv.inv hb
  simpa only [commutatorElement_def, inv_inv, sourceCommutator] using
    quotient_commutator_independent ha' hb'

theorem bracket_eq_of_lifts (ell : ℕ) (F : Type*) [Field F]
    (x y : PiA ell F) (a b : ProEll ell F)
    (ha : QuotientGroup.mk' _ a = x) (hb : QuotientGroup.mk' _ b = y) :
    (bracket ell F x y : PiC ell F) =
      QuotientGroup.mk' _ (sourceCommutator a b) := by
  exact sourceCommutator_independent ((abelianLift_spec ell F x).trans ha.symm)
    ((abelianLift_spec ell F y).trans hb.symm)

theorem quotient_nonarchimedean {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] : NonarchimedeanGroup (G ⧸ N) where
  is_nonarchimedean U hU := by
    let q := QuotientGroup.mk' N
    have hpre : q ⁻¹' U ∈ nhds (1 : G) := by
      apply (QuotientGroup.continuous_mk.continuousAt :
        ContinuousAt (fun x : G => (QuotientGroup.mk x : G ⧸ N)) 1).preimage_mem_nhds
      simpa using hU
    obtain ⟨V, hV, hVo, h1V⟩ := mem_nhds_iff.mp hpre
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo h1V
    refine ⟨{ H.toSubgroup.map q with
      isOpen' := QuotientGroup.isOpenMap_coe _ H.isOpen }, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact hV (hH hg)

theorem proEllKernel_isClosed (ell : ℕ) (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : IsClosed (proEllKernel ell G : Set G) := by
  simp only [proEllKernel, Subgroup.coe_iInf]
  exact isClosed_iInter fun H => isClosed_iInter fun _ => H.toOpenSubgroup.isClosed

theorem restrictScalarsHom_continuous {F P A : Type*} [Field F] [Field P] [Field A]
    [Algebra F P] [Algebra P A] [Algebra F A] [IsScalarTower F P A]
    [Algebra.IsAlgebraic P A] :
    Continuous (AlgEquiv.restrictScalarsHom F : (A ≃ₐ[P] A) →* (A ≃ₐ[F] A)) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, heU⟩ := hU
  let : FiniteDimensional F E := hE
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := F) (A := E))
  let S : Set A := (algebraMap E A) '' (s : Set E)
  have hS : S.Finite := s.finite_toSet.image _
  let : Finite S := hS.to_subtype
  let E' := IntermediateField.adjoin P S
  have : FiniteDimensional P E' := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := P) x).isIntegral)
  apply (krullTopology_mem_nhds_one_iff P A _).mpr
  refine ⟨E', inferInstance, ?_⟩
  intro σ hσ
  apply heU
  change (σ.restrictScalars F) ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have heq : ((σ.restrictScalars F).toAlgHom.comp E.val) = E.val := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro x hx
    exact ((IntermediateField.mem_fixingSubgroup_iff E' σ).mp hσ) _
      (IntermediateField.subset_adjoin P S ⟨x, hx, rfl⟩)
  intro x hx
  exact DFunLike.congr_fun heq ⟨x, hx⟩

theorem restrictScalarsHom_surjective_of_purelyInseparable {F P A : Type*}
    [Field F] [Field P] [Field A] [Algebra F P] [Algebra P A] [Algebra F A]
    [IsScalarTower F P A] [IsPurelyInseparable F P] :
    Function.Surjective (AlgEquiv.restrictScalarsHom F : (A ≃ₐ[P] A) →* (A ≃ₐ[F] A)) := by
  intro σ
  have hfix : σ.toAlgHom.comp (IsScalarTower.toAlgHom F P A) =
      IsScalarTower.toAlgHom F P A := Subsingleton.elim _ _
  refine ⟨{ σ.toRingEquiv with commutes' := fun p => DFunLike.congr_fun hfix p }, ?_⟩
  ext x
  rfl

theorem absoluteGaloisGroup_compact (F : Type*) [Field F] :
    CompactSpace (Field.absoluteGaloisGroup F) := by
  let P := perfectClosure F (AlgebraicClosure F)
  have : Algebra.IsAlgebraic P (AlgebraicClosure F) :=
    Algebra.IsAlgebraic.tower_top (K := F) P
  have : Normal P (AlgebraicClosure F) := ⟨fun x => IsAlgClosed.splits _⟩
  have : IsGalois P (AlgebraicClosure F) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  change CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
  exact Function.Surjective.compactSpace
    (restrictScalarsHom_continuous (F := F) (P := P) (A := AlgebraicClosure F))
    (restrictScalarsHom_surjective_of_purelyInseparable (F := F) (P := P)
      (A := AlgebraicClosure F))

theorem absoluteGaloisGroup_nonarchimedean (F : Type*) [Field F] :
    NonarchimedeanGroup (Field.absoluteGaloisGroup F) where
  is_nonarchimedean U hU := by
    change U ∈ nhds (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) at hU
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F (AlgebraicClosure F) U).mp hU
    let := hE
    exact ⟨{ E.fixingSubgroup with isOpen' := E.fixingSubgroup_isOpen }, hEU⟩

instance (F : Type*) [Field F] : CompactSpace (Field.absoluteGaloisGroup F) :=
  absoluteGaloisGroup_compact F

instance (F : Type*) [Field F] : NonarchimedeanGroup (Field.absoluteGaloisGroup F) :=
  absoluteGaloisGroup_nonarchimedean F

instance (F : Type*) [Field F] : T2Space (Field.absoluteGaloisGroup F) := by
  change T2Space (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
  infer_instance

instance ProEll.t2Space (ell : ℕ) (F : Type*) [Field F] : T2Space (ProEll ell F) := by
  have := proEllKernel_isClosed ell (Field.absoluteGaloisGroup F)
  infer_instance

instance ProEll.totallyDisconnectedSpace (ell : ℕ) (F : Type*) [Field F] :
    TotallyDisconnectedSpace (ProEll ell F) := by
  have := quotient_nonarchimedean (proEllKernel ell (Field.absoluteGaloisGroup F))
  infer_instance

instance PiA.t2Space (ell : ℕ) (F : Type*) [Field F] : T2Space (PiA ell F) := by
  have := Subgroup.isClosed_topologicalClosure (commutator (ProEll ell F))
  infer_instance

instance PiA.totallyDisconnectedSpace (ell : ℕ) (F : Type*) [Field F] :
    TotallyDisconnectedSpace (PiA ell F) := by
  have := quotient_nonarchimedean (commutator (ProEll ell F)).topologicalClosure
  infer_instance

instance PiC.t2Space (ell : ℕ) (F : Type*) [Field F] : T2Space (PiC ell F) := by
  have : IsClosed (closedGammaThree (ProEll ell F) : Set (ProEll ell F)) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

instance PiC.totallyDisconnectedSpace (ell : ℕ) (F : Type*) [Field F] :
    TotallyDisconnectedSpace (PiC ell F) := by
  have := quotient_nonarchimedean (closedGammaThree (ProEll ell F))
  infer_instance

open Filter

def EllQuotients (ell : ℕ) (G : Type*) [Group G] [TopologicalSpace G] :=
  {H : OpenNormalSubgroup G // IsPGroup ell (G ⧸ H.toSubgroup)}

instance ellQuotient_normal {ell : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (H : EllQuotients ell G) : H.1.toSubgroup.Normal := H.1.isNormal'

theorem proEllKernel_le {ell : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (H : EllQuotients ell G) : proEllKernel ell G ≤ H.1.toSubgroup := by
  exact iInf_le_of_le H.1 (iInf_le _ H.2)

def proEllEval {ell : ℕ} {G : Type*} [Group G] [TopologicalSpace G] :
    (G ⧸ proEllKernel ell G) →* (∀ H : EllQuotients ell G, G ⧸ H.1.toSubgroup) :=
  MonoidHom.pi fun H => QuotientGroup.map _ _ (MonoidHom.id G) (proEllKernel_le H)

theorem proEllEval_injective {ell : ℕ} {G : Type*} [Group G] [TopologicalSpace G] :
    Function.Injective (proEllEval (ell := ell) (G := G)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro z hz
  rw [Subgroup.mem_bot]
  induction z using QuotientGroup.induction_on with | H x =>
    apply (QuotientGroup.eq_one_iff x).mpr
    simp only [proEllKernel, Subgroup.mem_iInf]
    intro H hH
    exact (QuotientGroup.eq_one_iff x).mp (congrFun hz ⟨H, hH⟩)

theorem proEllEval_continuous {ell : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] : Continuous (proEllEval (ell := ell) (G := G)) := by
  apply continuous_pi
  intro H
  apply (QuotientGroup.isQuotientMap_mk (proEllKernel ell G)).continuous_iff.mpr
  exact QuotientGroup.continuous_mk

theorem proEllEval_isClosedEmbedding {ell : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] :
    Topology.IsClosedEmbedding (proEllEval (ell := ell) (G := G)) := by
  have (H : EllQuotients ell G) : DiscreteTopology (G ⧸ H.1.toSubgroup) :=
    QuotientGroup.discreteTopology H.1.isOpen
  exact proEllEval_continuous.isClosedEmbedding proEllEval_injective

theorem proEll_pow_tendsto_one {ell : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (x : G ⧸ proEllKernel ell G) :
    Tendsto (fun n : ℕ => x ^ ell ^ n) atTop (nhds 1) := by
  apply proEllEval_isClosedEmbedding.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro H
  obtain ⟨k, hk⟩ := H.2 (proEllEval x H)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  change (1 : G ⧸ H.1.toSubgroup) = proEllEval (x ^ ell ^ n) H
  rw [map_pow]
  change 1 = (proEllEval x H) ^ ell ^ n
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, pow_mul, hk, one_pow]

theorem isPGroup_of_proEll_image {ell : ℕ} {G A Q : Type*} [Group G] [Group A] [Group Q]
    [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace Q]
    [IsTopologicalGroup G] [CompactSpace G] [DiscreteTopology Q]
    (f : (G ⧸ proEllKernel ell G) →* A) (hf : Continuous f) (hs : Function.Surjective f)
    (q : A →* Q) (hq : Continuous q) (hqs : Function.Surjective q) : IsPGroup ell Q := by
  intro y
  obtain ⟨a, rfl⟩ := hqs y
  obtain ⟨x, rfl⟩ := hs a
  have ht := (hq.tendsto (f 1)).comp ((hf.tendsto 1).comp (proEll_pow_tendsto_one x))
  simp only [Function.comp_def, map_one, map_pow] at ht
  have he : ∀ᶠ n : ℕ in atTop, q (f x) ^ ell ^ n = 1 :=
    (tendsto_pure.mp (by simpa only [nhds_discrete, QuotientAddGroup.mk'_apply] using ht))
  exact he.exists

variable {ell : ℕ} [Fact ell.Prime]

theorem continuous_padic_toZModPow (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := ell) n) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero, (nhds_discrete (ZMod (ell ^ n))), tendsto_pure]
  have hpos : 0 < (ell : ℝ) := Nat.cast_pos.mpr (Fact.out : ell.Prime).pos
  have hr : (ell : ℝ) ^ (-(n : ℤ)) ≠ 0 := zpow_ne_zero _ (ne_of_gt hpos)
  have hb := (IsUltrametricDist.isOpen_closedBall (0 : PadicInt ell) hr).mem_nhds
    (Metric.mem_closedBall_self (le_of_lt (by positivity : (0 : ℝ) < ell ^ (-(n : ℤ)))))
  filter_upwards [hb] with x hx
  apply RingHom.mem_ker.mp
  rw [PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx

omit [Fact ell.Prime] in
theorem finite_abelian_ell_exponent {A : Type*} [AddCommGroup A] [Finite A]
    (h : IsPGroup ell (Multiplicative A)) : ∃ n, ∀ x : A, ell ^ n • x = 0 := by
  obtain ⟨n, hn⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp h
  exact ⟨n, fun x => congrArg Multiplicative.toAdd (hn (Multiplicative.ofAdd x))⟩

abbrev finiteEllModule {A : Type*} [AddCommGroup A] [Finite A]
    (h : IsPGroup ell (Multiplicative A)) : Module (PadicInt ell) A := by
  let n := (finite_abelian_ell_exponent h).choose
  letI := AddCommGroup.zmodModule (finite_abelian_ell_exponent h).choose_spec
  exact Module.compHom A (PadicInt.toZModPow n)

theorem finiteEllModule_continuous {A : Type*} [AddCommGroup A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (h : IsPGroup ell (Multiplicative A)) :
    letI := finiteEllModule h
    ContinuousSMul (PadicInt ell) A := by
  let n := (finite_abelian_ell_exponent h).choose
  let := AddCommGroup.zmodModule (finite_abelian_ell_exponent h).choose_spec
  let : ContinuousSMul (ZMod (ell ^ n)) A := ⟨continuous_of_discreteTopology⟩
  exact MulAction.continuousSMul_compHom (continuous_padic_toZModPow n)

section Profinite
variable {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [NonarchimedeanAddGroup A] [CompactSpace A] [T2Space A]

abbrev AllLevels (A : Type*) [AddCommGroup A] [TopologicalSpace A] :=
  ∀ H : OpenAddSubgroup A, A ⧸ H.toAddSubgroup

instance levelDiscrete (H : OpenAddSubgroup A) :
    DiscreteTopology (A ⧸ H.toAddSubgroup) := QuotientAddGroup.discreteTopology H.isOpen

instance levelFinite (H : OpenAddSubgroup A) :
    Finite (A ⧸ H.toAddSubgroup) := finite_of_compact_of_discrete

def levelEval : A →+ AllLevels A :=
  AddMonoidHom.pi fun H => QuotientAddGroup.mk' H.toAddSubgroup

omit [CompactSpace A] in
theorem levelEval_injective : Function.Injective (levelEval (A := A)) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  rw [AddSubgroup.mem_bot]
  by_contra h
  have hU : {x}ᶜ ∈ nhds (0 : A) := isClosed_singleton.isOpen_compl.mem_nhds (by simpa using Ne.symm h)
  obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hU
  have hxH : x ∈ H := (QuotientAddGroup.eq_zero_iff x).mp (congrFun hx H)
  exact hH hxH (Set.mem_singleton x)

omit [NonarchimedeanAddGroup A] [CompactSpace A] [T2Space A] in
theorem levelEval_continuous : Continuous (levelEval (A := A)) :=
  continuous_pi fun _ => QuotientAddGroup.continuous_mk

theorem levelEval_closedEmbedding :
    Topology.IsClosedEmbedding (levelEval (A := A)) :=
  levelEval_continuous.isClosedEmbedding levelEval_injective

def AllLevelsEll (ell : ℕ) (A : Type*) [AddCommGroup A] [TopologicalSpace A] : Prop :=
  ∀ H : OpenAddSubgroup A, IsPGroup ell (Multiplicative (A ⧸ H.toAddSubgroup))

variable [hA : Fact (AllLevelsEll ell A)]

instance levelsModule : Module (PadicInt ell) (AllLevels A) := by
  letI (H : OpenAddSubgroup A) := finiteEllModule (hA.out H)
  exact Pi.module _ _ _

omit [T2Space A] in
theorem levels_continuous : ContinuousSMul (PadicInt ell) (AllLevels A) := by
  let (H : OpenAddSubgroup A) := finiteEllModule (hA.out H)
  let (H : OpenAddSubgroup A) := finiteEllModule_continuous (hA.out H)
  infer_instance

def levelImage : Submodule (PadicInt ell) (AllLevels A) where
  carrier := Set.range (levelEval (A := A))
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add _ _ _⟩
  smul_mem' := by
    let := levels_continuous (ell := ell) (A := A)
    rintro c _ ⟨x, rfl⟩
    refine (PadicInt.denseRange_natCast (p := ell)).induction_on c ?_ ?_
    · exact levelEval_closedEmbedding.isClosed_range.preimage (continuous_id.smul continuous_const)
    · intro n
      exact ⟨n • x, by simp [Nat.cast_smul_eq_nsmul]⟩

def levelImageEquiv : A ≃+ levelImage (ell := ell) (A := A) :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨levelEval x, ⟨x, rfl⟩⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' := fun x y => Subtype.ext (map_add _ x y) } : A →+ levelImage (ell := ell))
    ⟨fun _ _ h => levelEval_injective (congrArg Subtype.val h), by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩⟩

abbrev abelianEllModule : Module (PadicInt ell) A :=
  (levelImageEquiv (ell := ell) (A := A)).module (PadicInt ell)

theorem levelEval_smul (c : PadicInt ell) (x : A) :
    letI := abelianEllModule (ell := ell) (A := A)
    levelEval (c • x) = c • levelEval x := by
  let := abelianEllModule (ell := ell) (A := A)
  exact congrArg Subtype.val
    (((levelImageEquiv (ell := ell) (A := A)).linearEquiv (PadicInt ell)).map_smul c x)

theorem abelianEllModule_continuous :
    letI := abelianEllModule (ell := ell) (A := A)
    ContinuousSMul (PadicInt ell) A := by
  let := abelianEllModule (ell := ell) (A := A)
  let := levels_continuous (ell := ell) (A := A)
  constructor
  apply levelEval_closedEmbedding.isEmbedding.continuous_iff.mpr
  change Continuous (fun z : PadicInt ell × A => levelEval (z.1 • z.2))
  simp_rw [levelEval_smul]
  exact continuous_fst.smul (levelEval_continuous.comp continuous_snd)

end Profinite

end BogomolovPop

end
end

end OAI


