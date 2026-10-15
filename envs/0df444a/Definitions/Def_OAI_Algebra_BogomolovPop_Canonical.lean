-- Prove2me | Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
-- name    : OAI_Algebra_BogomolovPop_Canonical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:20:44.753696+00:00
-- url     : https://prove2.me/theorems/f0bcdf29-1697-42d9-9d14-eb9de405fb7e
-- title:
--   Galois conjugation along isomorphisms of perfect closures and the canonical map to $\mathbb{Z}_\ell^\times$-classes of abelian Galois isomorphisms
-- statement:
--   This file transports absolute Galois groups along isomorphisms of perfect closures and builds the canonical map from Frobenius classes of field isomorphisms to $\mathbb{Z}_\ell^\times$-classes of bracket-compatible isomorphisms between abelianized pro-$\ell$ Galois groups.
--
--   Notation follows the foundational Galois definitions: for a field $F$, $\overline{F}$ is its algebraic closure, $F^{\mathrm{perf}}\subseteq\overline{F}$ the perfect closure of $F$ in $\overline{F}$, $G_F=\operatorname{Aut}_F(\overline{F})$, $\mathcal{G}_F$ the maximal pro-$\ell$ quotient of $G_F$, $\Pi^a_F$ its topological abelianization with projection $\pi_F:G_F\to\Pi^a_F$, $\Pi^c_F=\mathcal{G}_F/\overline{\gamma}_3(\mathcal{G}_F)$, $\Delta_F=\ker(\Pi^c_F\to\Pi^a_F)$ and $[\cdot,\cdot]:\Pi^a_F\times\Pi^a_F\to\Delta_F$ the commutator bracket. For fields $k\subseteq K$ and $l\subseteq L$, $\operatorname{Isom}(k,K;l,L)$ is the set of ring isomorphisms $\alpha:K^{\mathrm{perf}}\to L^{\mathrm{perf}}$ mapping the image of $k$ onto the image of $l$, and $\operatorname{Isom}^c_\ell(K,L)$ is the set of topological isomorphisms $\phi:\Pi^a_L\to\Pi^a_K$ that are *bracket-compatible*: some topological isomorphism $\psi:\Delta_L\to\Delta_K$ satisfies $\psi([x,y])=[\phi(x),\phi(y)]$ for all $x,y\in\Pi^a_L$.
--
--   1. **$\ell$-adic structure.** For every field $F$, the abelian group $\Pi^a_F$ is non-archimedean and all its quotients by open subgroups are $\ell$-groups. The subgroup $\Delta_F$ is central in $\Pi^c_F$, hence abelian; it is compact and non-archimedean, $\Pi^c_F$ is non-archimedean, and $x^{\ell^n}\to 1$ as $n\to\infty$ for every $x$ in $\Pi^c_F$ or in $\Delta_F$. Consequently, for $\ell$ prime, $\Pi^a_F$ and $\Delta_F$, written additively, carry the canonical $\mathbb{Z}_\ell$-module structure of abelian pro-$\ell$ groups, with continuous scalar multiplication.
--   2. **Scalar automorphisms.** If $R$ is a commutative topological ring, $G$ a commutative topological group whose additive version is an $R$-module with continuous scalar multiplication, and $u\in R^\times$, then $x\mapsto u\cdot x$ (in multiplicative notation $x\mapsto x^u$) is an automorphism of the topological group $G$.
--   3. **Functoriality of the quotients.** A continuous homomorphism $f:G\to H$ of topological groups maps $N_\ell(G)$, $\overline{[G,G]}$ and $\overline{\gamma}_3(G)$ into $N_\ell(H)$, $\overline{[H,H]}$ and $\overline{\gamma}_3(H)$. Hence a topological isomorphism $f:G\to H$ induces topological isomorphisms between the maximal pro-$\ell$ quotients, between the topological abelianizations and between the quotients by $\overline{\gamma}_3$ (more generally, $G/N\cong H/M$ whenever $f(N)\subseteq M$ and $f^{-1}(M)\subseteq N$). For a topological isomorphism $f:\mathcal{G}_L\to\mathcal{G}_K$, the induced isomorphism $\Pi^c_L\to\Pi^c_K$ restricts to a topological isomorphism $\Delta_L\to\Delta_K$, and the induced isomorphism $\Pi^a_L\to\Pi^a_K$ is bracket-compatible.
--   4. **Extending isomorphisms of perfect closures.** $\overline{F}$ is an algebraic closure of $F^{\mathrm{perf}}$, so every ring isomorphism $\alpha:K^{\mathrm{perf}}\to L^{\mathrm{perf}}$ extends to a ring isomorphism $\tilde\alpha:\overline{K}\to\overline{L}$; one such extension is fixed. Every element of $G_F$ fixes $F^{\mathrm{perf}}$ pointwise.
--   5. **Galois conjugation.** If $\beta:\overline{K}\to\overline{L}$ is any ring isomorphism extending $\alpha$, then
--   $$c_\beta:G_L\to G_K,\qquad c_\beta(\sigma)=\beta^{-1}\circ\sigma\circ\beta,$$
--   is a well-defined isomorphism of topological groups; its inverse is the conjugation built from $\alpha^{-1}$ and $\beta^{-1}$.
--   6. **Induced abelian isomorphism.** For $\beta$ as in item 5, $\Phi_\beta\in\operatorname{Isom}^c_\ell(K,L)$ is the isomorphism $\Pi^a_L\to\Pi^a_K$ induced by $c_\beta$ through the maximal pro-$\ell$ quotients and the abelianizations, so that $\Phi_\beta(\pi_L(\sigma))=\pi_K(c_\beta(\sigma))$. The projection $\pi_F$ is surjective. If $\beta$ and $\gamma$ both extend $\alpha$, then $\varepsilon=\gamma^{-1}\circ\beta$ lies in $G_K$, $c_\gamma(\sigma)=\varepsilon\,c_\beta(\sigma)\,\varepsilon^{-1}$ for all $\sigma\in G_L$, and $\Phi_\beta=\Phi_\gamma$.
--   7. **Canonical pullback.** For $\alpha\in\operatorname{Isom}(k,K;l,L)$ put $\Phi(\alpha)=\Phi_{\tilde\alpha}$. If $\alpha'$ arises from $\alpha$ by a Frobenius step, i.e. $\alpha'(x)=\alpha(x)^p$ for all $x\in K^{\mathrm{perf}}$ for some prime $p$ with $p=0$ in $L$, then $\Phi(\alpha')=\Phi(\alpha)$; therefore $\Phi$ is constant on the classes of the equivalence relation generated by Frobenius steps.
--   8. **The canonical map on orbit sets.** Let $\ell$ be prime. Let $\operatorname{Isom}^F(k,K;l,L)$ be the quotient of $\operatorname{Isom}(k,K;l,L)$ by the equivalence relation generated by Frobenius steps, and $\operatorname{Isom}^c_\ell(K,L)/\mathbb{Z}_\ell^\times$ the quotient of $\operatorname{Isom}^c_\ell(K,L)$ by the equivalence relation generated by scalar steps: $\phi$ steps to $\chi$ if for some $u\in\mathbb{Z}_\ell^\times$ and all $x$, $\chi(x)=\lim_{n\to\infty}\phi(x)^{a_n(u)}$, where $a_n(u)\in\{0,\dots,\ell^n-1\}$ is congruent to $u$ modulo $\ell^n$. The canonical map is
--   $$\overline{\Phi}:\operatorname{Isom}^F(k,K;l,L)\to\operatorname{Isom}^c_\ell(K,L)/\mathbb{Z}_\ell^\times,\qquad [\alpha]\mapsto[\Phi(\alpha)].$$
--
--   The map $\overline{\Phi}$ is the central object of the Bogomolov–Pop type injectivity result for function fields over algebraically closed fields: there one shows that a Frobenius class of isomorphisms of perfect closures is determined by the induced isomorphism of abelianized pro-$\ell$ Galois groups up to $\ell$-adic units. Items 5 and 6 are also what identify any isomorphism $\phi$ that is Galois-compatible with an extension of $\alpha$ with the canonical pullback $\Phi(\alpha)$.
--
--   **Formalization Note** $\operatorname{Isom}(k,K;l,L)$, $\operatorname{Isom}^F$, $\operatorname{Isom}^c_\ell$ and $\operatorname{Isom}^c_\ell/\mathbb{Z}_\ell^\times$ are `PerfectIsom`, `IsomF`, `IsomC` and `IsomCUnits` of the base definitions, and $F^{\mathrm{perf}}$ is `PerfectFieldClosure F`, the relative perfect closure inside `AlgebraicClosure F`. The module structures of item 1 are the instances `PiA.padicModule` and `Delta.padicModule` on `Additive (PiA ell F)` and `Additive (Delta ell F)`. Item 2 is `unitScalarEquiv`; item 3 consists of `quotientContinuousEquiv`, `proEllContinuousEquiv`, `abelianContinuousEquiv`, `centralContinuousEquiv`, `deltaContinuousEquiv` and `induced_bracketCompatible`. The fixed extension $\tilde\alpha$ is `extendPerfectEquiv`, obtained from `IsAlgClosure.equivOfEquiv` and hence a noncanonical choice; $c_\beta$ is `absoluteConjugate` (as a topological isomorphism, `absoluteConjugateContinuousEquiv`); $\Phi_\beta$ is `isomCOfExtension`, $\varepsilon$ is `extensionDifference`, $\Phi$ is `canonicalPullback`, and $\overline{\Phi}$ is `canonicalPhi`, defined with `Quotient.lift` using `canonicalPullback_eq_of_frobeniusOrbit`. Items 3 to 7 need no primality of $\ell$, and items 4 to 7 hold for arbitrary fields, without using the condition that $\alpha$ maps $k$ onto $l$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/BogomolovPop/Canonical.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/BogomolovPop/Canonical.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BogomolovPopInjectivity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations

namespace OAI

/-! Canonical Galois transport, bracket compatibility and quotient-map well-definedness. -/

noncomputable section
open scoped Topology

namespace BogomolovPop
open scoped Topology commutatorElement
open Filter

instance PiA.nonarchimedean (ell : ℕ) (F : Type*) [Field F] :
    NonarchimedeanGroup (PiA ell F) :=
  quotient_nonarchimedean (commutator (ProEll ell F)).topologicalClosure

instance additive_nonarchimedean (G : Type*) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] : NonarchimedeanAddGroup (Additive G) where
  is_nonarchimedean U hU := by
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean (G := G) U hU
    exact ⟨{ V.toSubgroup.toAddSubgroup with isOpen' := V.isOpen }, hV⟩

instance PiA.allLevelsEll (ell : ℕ) (F : Type*) [Field F] :
    Fact (AllLevelsEll ell (Additive (PiA ell F))) := ⟨by
  intro H
  let q : PiA ell F →* Multiplicative (Additive (PiA ell F) ⧸ H.toAddSubgroup) :=
    { toFun := fun x => Multiplicative.ofAdd (QuotientAddGroup.mk (Additive.ofMul x))
      map_one' := by rfl
      map_mul' := fun x y => by rfl }
  have hq : Continuous q :=
    (QuotientAddGroup.continuous_mk :
      Continuous (QuotientAddGroup.mk : Additive (PiA ell F) → Additive (PiA ell F) ⧸ H.toAddSubgroup))
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd y)
    exact ⟨Additive.toMul x, hx⟩
  exact isPGroup_of_proEll_image (QuotientGroup.mk' _) QuotientGroup.continuous_mk
    QuotientGroup.mk_surjective q hq hqs⟩

instance PiA.padicModule (ell : ℕ) [Fact ell.Prime] (F : Type*) [Field F] :
    Module (PadicInt ell) (Additive (PiA ell F)) := abelianEllModule

instance PiA.padicContinuousSMul (ell : ℕ) [Fact ell.Prime] (F : Type*) [Field F] :
    ContinuousSMul (PadicInt ell) (Additive (PiA ell F)) := abelianEllModule_continuous

instance PiA.additiveT2 (ell : ℕ) (F : Type*) [Field F] :
    T2Space (Additive (PiA ell F)) := PiA.t2Space ell F

theorem delta_commute {ell : ℕ} {F : Type*} [Field F]
    (z : Delta ell F) (x : PiC ell F) : Commute (z : PiC ell F) x := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (closedGammaThree (ProEll ell F)) z.1
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (closedGammaThree (ProEll ell F)) x
  rw [← ha]
  apply closedCommutator_image_commute
  apply (QuotientGroup.eq_one_iff a).mp
  have hz := z.property
  rw [← ha] at hz
  exact hz

instance Delta.commGroup (ell : ℕ) (F : Type*) [Field F] : CommGroup (Delta ell F) :=
  { (inferInstance : Group (Delta ell F)) with
    mul_comm := fun z x => Subtype.ext (delta_commute z x).eq }

theorem centralProjection_continuous (ell : ℕ) (F : Type*) [Field F] :
    Continuous (centralProjection ell F) := by
  apply (QuotientGroup.isQuotientMap_mk (closedGammaThree (ProEll ell F))).continuous_iff.mpr
  exact QuotientGroup.continuous_mk

instance Delta.compactSpace (ell : ℕ) (F : Type*) [Field F] : CompactSpace (Delta ell F) := by
  have h : IsClosed ((centralProjection ell F).ker : Set (PiC ell F)) :=
    isClosed_singleton.preimage (centralProjection_continuous ell F)
  exact isCompact_iff_compactSpace.mp h.isCompact

instance PiC.nonarchimedean (ell : ℕ) (F : Type*) [Field F] :
    NonarchimedeanGroup (PiC ell F) := quotient_nonarchimedean _

instance Delta.nonarchimedean (ell : ℕ) (F : Type*) [Field F] :
    NonarchimedeanGroup (Delta ell F) where
  is_nonarchimedean U hU := by
    obtain ⟨V, hV, hVo, h1V⟩ := mem_nhds_iff.mp hU
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo h1V
    exact ⟨H.toOpenSubgroup, hH.trans hV⟩

theorem PiC.pow_tendsto_one {ell : ℕ} {F : Type*} [Field F] (x : PiC ell F) :
    Tendsto (fun n : ℕ => x ^ ell ^ n) atTop (nhds 1) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (closedGammaThree (ProEll ell F)) x
  have hq : Continuous (QuotientGroup.mk' (closedGammaThree (ProEll ell F))) :=
    QuotientGroup.continuous_mk
  simpa only [map_one, Function.comp_def, map_pow] using
    (hq.tendsto (1 : ProEll ell F)).comp (proEll_pow_tendsto_one a)

theorem Delta.pow_tendsto_one {ell : ℕ} {F : Type*} [Field F] (x : Delta ell F) :
    Tendsto (fun n : ℕ => x ^ ell ^ n) atTop (nhds 1) := by
  apply Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
  exact PiC.pow_tendsto_one x.1

instance Delta.allLevelsEll (ell : ℕ) (F : Type*) [Field F] :
    Fact (AllLevelsEll ell (Additive (Delta ell F))) := ⟨by
  intro H y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd y)
  have hq : Continuous (QuotientAddGroup.mk' H.toAddSubgroup) :=
    QuotientAddGroup.continuous_mk
  have hx : Tendsto (fun n : ℕ => ell ^ n • x) atTop (nhds 0) :=
    Delta.pow_tendsto_one (Additive.toMul x)
  have ht := (hq.tendsto (0 : Additive (Delta ell F))).comp hx
  simp only [Function.comp_def, map_zero] at ht
  have he : ∀ᶠ n : ℕ in atTop,
      (QuotientAddGroup.mk (ell ^ n • x) : Additive (Delta ell F) ⧸ H.toAddSubgroup) = 0 := by
    exact tendsto_pure.mp (by simpa only [nhds_discrete, QuotientAddGroup.mk'_apply] using ht)
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨n, hn⟩⟩

instance Delta.additiveT2 (ell : ℕ) (F : Type*) [Field F] :
    T2Space (Additive (Delta ell F)) := inferInstanceAs (T2Space (Delta ell F))

instance Delta.padicModule (ell : ℕ) [Fact ell.Prime] (F : Type*) [Field F] :
    Module (PadicInt ell) (Additive (Delta ell F)) := abelianEllModule

instance Delta.padicContinuousSMul (ell : ℕ) [Fact ell.Prime] (F : Type*) [Field F] :
    ContinuousSMul (PadicInt ell) (Additive (Delta ell F)) := abelianEllModule_continuous

def unitScalarEquiv {R G : Type*} [CommRing R] [TopologicalSpace R]
    [CommGroup G] [TopologicalSpace G] [Module R (Additive G)]
    [ContinuousSMul R (Additive G)] (u : Rˣ) : G ≃ₜ* G where
  toMulEquiv := (DistribMulAction.toAddEquiv (Additive G) u).toMultiplicative
  continuous_toFun := by
    change Continuous (fun x : Additive G => (u : R) • x)
    exact continuous_const.smul continuous_id
  continuous_invFun := by
    change Continuous (fun x : Additive G => ((u⁻¹ : Rˣ) : R) • x)
    exact continuous_const.smul continuous_id

@[simp] theorem unitScalarEquiv_apply {R G : Type*} [CommRing R] [TopologicalSpace R]
    [CommGroup G] [TopologicalSpace G] [Module R (Additive G)]
    [ContinuousSMul R (Additive G)] (u : Rˣ) (x : G) :
    unitScalarEquiv u x = Additive.toMul ((u : R) • Additive.ofMul x) := rfl

end BogomolovPop

namespace BogomolovPop
open scoped Topology commutatorElement

theorem quotient_comap_map_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (N : Subgroup H) [N.Normal] :
    Function.Injective (QuotientGroup.map (N.comap f) N f le_rfl) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro z hz
  rw [Subgroup.mem_bot]
  induction z using QuotientGroup.induction_on with | H x =>
    apply (QuotientGroup.eq_one_iff x).mpr
    exact (QuotientGroup.eq_one_iff (f x)).mp hz

theorem proEllKernel_map_le {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (ell : ℕ) (f : G →* H)
    (hf : Continuous f) : proEllKernel ell G ≤ (proEllKernel ell H).comap f := by
  intro x hx
  simp only [proEllKernel, Subgroup.mem_comap, Subgroup.mem_iInf] at hx ⊢
  intro N hN
  let U : OpenNormalSubgroup G :=
    { N.toOpenSubgroup.comap f hf with
      isNormal' := by
        change (N.toSubgroup.comap f).Normal
        infer_instance }
  have : U.toSubgroup.Normal := U.isNormal'
  have hU : IsPGroup ell (G ⧸ U.toSubgroup) :=
    hN.of_injective (QuotientGroup.map (N.toSubgroup.comap f) N.toSubgroup f le_rfl)
      (quotient_comap_map_injective f N.toSubgroup)
  exact hx U hU

theorem continuous_quotientMap {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (N : Subgroup G) (M : Subgroup H)
    [N.Normal] [M.Normal] (f : G →* H) (h : N ≤ M.comap f) (hf : Continuous f) :
    Continuous (QuotientGroup.map N M f h) := by
  apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp hf

theorem closedCommutator_map_le {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]
    [IsTopologicalGroup H] (f : G →* H) (hf : Continuous f) :
    (commutator G).topologicalClosure ≤ ((commutator H).topologicalClosure).comap f := by
  apply Subgroup.topologicalClosure_minimal
  · rw [_root_.commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    change f ⁅x, y⁆ ∈ (commutator H).topologicalClosure
    rw [map_commutatorElement]
    exact Subgroup.le_topologicalClosure _
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  · exact (Subgroup.isClosed_topologicalClosure _).preimage hf

theorem closedGammaThree_map_le {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]
    [IsTopologicalGroup H] (f : G →* H) (hf : Continuous f) :
    closedGammaThree G ≤ (closedGammaThree H).comap f := by
  apply Subgroup.topologicalClosure_minimal
  · apply Subgroup.commutator_le.mpr
    intro x hx y _
    change f ⁅x, y⁆ ∈ closedGammaThree H
    rw [map_commutatorElement]
    exact Subgroup.le_topologicalClosure _
      (Subgroup.commutator_mem_commutator (closedCommutator_map_le f hf hx)
        (Subgroup.mem_top _))
  · exact (Subgroup.isClosed_topologicalClosure _).preimage hf

def quotientContinuousEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (N : Subgroup G) (M : Subgroup H)
    [N.Normal] [M.Normal] (f : G ≃ₜ* H)
    (hf : N ≤ M.comap f.toMonoidHom) (hi : M ≤ N.comap f.symm.toMonoidHom) :
    (G ⧸ N) ≃ₜ* (H ⧸ M) where
  toFun := QuotientGroup.map N M f.toMonoidHom hf
  invFun := QuotientGroup.map M N f.symm.toMonoidHom hi
  left_inv x := by
    induction x using QuotientGroup.induction_on with | H x =>
      change QuotientGroup.mk' N (f.symm (f x)) = QuotientGroup.mk' N x
      rw [f.symm_apply_apply]
  right_inv x := by
    induction x using QuotientGroup.induction_on with | H x =>
      change QuotientGroup.mk' M (f (f.symm x)) = QuotientGroup.mk' M x
      rw [f.apply_symm_apply]
  map_mul' := map_mul _
  continuous_toFun := continuous_quotientMap N M f.toMonoidHom hf f.continuous
  continuous_invFun := continuous_quotientMap M N f.symm.toMonoidHom hi f.symm.continuous

def proEllContinuousEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (ell : ℕ) (f : G ≃ₜ* H) :
    (G ⧸ proEllKernel ell G) ≃ₜ* (H ⧸ proEllKernel ell H) :=
  quotientContinuousEquiv _ _ f (proEllKernel_map_le ell f.toMonoidHom f.continuous)
    (proEllKernel_map_le ell f.symm.toMonoidHom f.symm.continuous)

def abelianContinuousEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]
    [IsTopologicalGroup H] (f : G ≃ₜ* H) :
    TopologicalAbelianization G ≃ₜ* TopologicalAbelianization H :=
  quotientContinuousEquiv _ _ f (closedCommutator_map_le f.toMonoidHom f.continuous)
    (closedCommutator_map_le f.symm.toMonoidHom f.symm.continuous)

def centralContinuousEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]
    [IsTopologicalGroup H] (f : G ≃ₜ* H) :
    (G ⧸ closedGammaThree G) ≃ₜ* (H ⧸ closedGammaThree H) :=
  quotientContinuousEquiv _ _ f (closedGammaThree_map_le f.toMonoidHom f.continuous)
    (closedGammaThree_map_le f.symm.toMonoidHom f.symm.continuous)

end BogomolovPop

noncomputable section
namespace BogomolovPop
open scoped Topology

theorem isAlgClosure_perfectClosure (F : Type*) [Field F] :
    IsAlgClosure (PerfectFieldClosure F) (AlgebraicClosure F) := by
  have : Algebra.IsAlgebraic (PerfectFieldClosure F) (AlgebraicClosure F) :=
    Algebra.IsAlgebraic.tower_top (K := F) (PerfectFieldClosure F)
  exact ⟨inferInstance, inferInstance⟩

def extendPerfectEquiv {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L) :
    AlgebraicClosure K ≃+* AlgebraicClosure L := by
  letI := isAlgClosure_perfectClosure K
  letI := isAlgClosure_perfectClosure L
  exact IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure L) α

theorem extendPerfectEquiv_spec {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L) (x : PerfectFieldClosure K) :
    extendPerfectEquiv α x = (α x : AlgebraicClosure L) := by
  let := isAlgClosure_perfectClosure K
  let := isAlgClosure_perfectClosure L
  exact IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure L) α x

theorem perfectClosure_fixed {F : Type*} [Field F]
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (x : PerfectFieldClosure F) :
    σ (x : AlgebraicClosure F) = x := by
  have h : σ.toAlgHom.comp (perfectClosure F (AlgebraicClosure F)).val =
      (perfectClosure F (AlgebraicClosure F)).val := Subsingleton.elim _ _
  exact DFunLike.congr_fun h x

def absoluteConjugate {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L))
    (σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K where
  toRingEquiv := (β.trans σ.toRingEquiv).trans β.symm
  commutes' x := by
    change β.symm (σ (β (algebraMap K (AlgebraicClosure K) x))) = _
    apply β.injective
    rw [β.apply_symm_apply]
    change σ (β ((algebraMap K (PerfectFieldClosure K) x : PerfectFieldClosure K) :
      AlgebraicClosure K)) = β _
    rw [hβ, perfectClosure_fixed]
    exact (hβ _).symm

@[simp] theorem absoluteConjugate_apply {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L))
    (σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (x : AlgebraicClosure K) :
    absoluteConjugate α β hβ σ x = β.symm (σ (β x)) := rfl

theorem perfectExtension_symm {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L)) :
    ∀ y : PerfectFieldClosure L, β.symm y = (α.symm y : AlgebraicClosure K) := by
  intro y
  apply β.injective
  rw [β.apply_symm_apply, hβ, α.apply_symm_apply]

def absoluteConjugateEquiv {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L)) :
    (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) ≃*
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  toFun := absoluteConjugate α β hβ
  invFun := absoluteConjugate α.symm β.symm (perfectExtension_symm α β hβ)
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp
  map_mul' σ τ := by ext x; simp [AlgEquiv.mul_apply]

theorem absoluteConjugate_continuous {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L)) :
    Continuous (absoluteConjugate α β hβ) := by
  change Continuous (absoluteConjugateEquiv α β hβ).toMonoidHom
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, heU⟩ := hU
  let : FiniteDimensional K E := hE
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := K) (A := E))
  let S : Set (AlgebraicClosure L) := (fun x : E => β (x : AlgebraicClosure K)) '' (s : Set E)
  have hS : S.Finite := s.finite_toSet.image _
  let : Finite S := hS.to_subtype
  let E' := IntermediateField.adjoin L S
  have : FiniteDimensional L E' := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := L) x).isIntegral)
  apply (krullTopology_mem_nhds_one_iff L (AlgebraicClosure L) _).mpr
  refine ⟨E', inferInstance, ?_⟩
  intro σ hσ
  apply heU
  change absoluteConjugate α β hβ σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have heq : (absoluteConjugate α β hβ σ).toAlgHom.comp E.val = E.val := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro x hx
    change β.symm (σ (β (x : AlgebraicClosure K))) = x
    rw [((IntermediateField.mem_fixingSubgroup_iff E' σ).mp hσ) _
      (IntermediateField.subset_adjoin L S ⟨x, hx, rfl⟩), β.symm_apply_apply]
  intro x hx
  exact DFunLike.congr_fun heq ⟨x, hx⟩

def absoluteConjugateContinuousEquiv {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L)) :
    Field.absoluteGaloisGroup L ≃ₜ* Field.absoluteGaloisGroup K where
  toMulEquiv := absoluteConjugateEquiv α β hβ
  continuous_toFun := absoluteConjugate_continuous α β hβ
  continuous_invFun := absoluteConjugate_continuous α.symm β.symm
    (perfectExtension_symm α β hβ)

end BogomolovPop

namespace BogomolovPop
open scoped Topology

theorem centralProjection_natural {ell : ℕ} {K L : Type*} [Field K] [Field L]
    (f : ProEll ell L ≃ₜ* ProEll ell K) (z : PiC ell L) :
    centralProjection ell K (centralContinuousEquiv f z) =
      abelianContinuousEquiv f (centralProjection ell L z) := by
  induction z using QuotientGroup.induction_on with | H z => rfl

def deltaContinuousEquiv {ell : ℕ} {K L : Type*} [Field K] [Field L]
    (f : ProEll ell L ≃ₜ* ProEll ell K) : Delta ell L ≃ₜ* Delta ell K where
  toFun x := ⟨centralContinuousEquiv f x, by
    change centralProjection ell K _ = 1
    rw [centralProjection_natural, x.property, map_one]⟩
  invFun x := ⟨(centralContinuousEquiv f).symm x, by
    change centralProjection ell L _ = 1
    apply (abelianContinuousEquiv f).injective
    rw [map_one, ← centralProjection_natural, ContinuousMulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := by ext; exact (centralContinuousEquiv f).symm_apply_apply x
  right_inv x := by ext; exact (centralContinuousEquiv f).apply_symm_apply x
  map_mul' x y := by ext; exact map_mul (centralContinuousEquiv f) (x : PiC ell L) (y : PiC ell L)
  continuous_toFun := Continuous.subtype_mk
    ((centralContinuousEquiv f).continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((centralContinuousEquiv f).symm.continuous.comp continuous_subtype_val) _

theorem induced_bracketCompatible {ell : ℕ} {K L : Type*} [Field K] [Field L]
    (f : ProEll ell L ≃ₜ* ProEll ell K) :
    BracketCompatible (abelianContinuousEquiv f) := by
  refine ⟨deltaContinuousEquiv f, ?_⟩
  intro σ τ
  apply Subtype.ext
  change centralContinuousEquiv f (bracket ell L σ τ : PiC ell L) = _
  rw [bracket_eq_of_lifts ell K _ _ (f (abelianLift ell L σ))
    (f (abelianLift ell L τ))]
  · change QuotientGroup.mk' _ (f (sourceCommutator (abelianLift ell L σ)
      (abelianLift ell L τ))) = _
    simp only [sourceCommutator, map_mul, map_inv]
  · change abelianContinuousEquiv f (QuotientGroup.mk' _ (abelianLift ell L σ)) = _
    rw [abelianLift_spec]
  · change abelianContinuousEquiv f (QuotientGroup.mk' _ (abelianLift ell L τ)) = _
    rw [abelianLift_spec]

def isomCOfExtension (ell : ℕ) {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L)) :
    IsomC ell K L :=
  ⟨abelianContinuousEquiv (proEllContinuousEquiv ell
      (absoluteConjugateContinuousEquiv α β hβ)), induced_bracketCompatible _⟩

end BogomolovPop

namespace BogomolovPop

 theorem absoluteToPiA_surjective (ell : ℕ) (F : Type*) [Field F] :
    Function.Surjective (absoluteToPiA ell F) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

def extensionDifference {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β γ : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L))
    (hγ : ∀ x : PerfectFieldClosure K, γ x = (α x : AlgebraicClosure L)) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K where
  toRingEquiv := β.trans γ.symm
  commutes' x := by
    change γ.symm (β (algebraMap K (AlgebraicClosure K) x)) = _
    apply γ.injective
    rw [γ.apply_symm_apply]
    exact (hβ (algebraMap K (PerfectFieldClosure K) x)).trans
      (hγ (algebraMap K (PerfectFieldClosure K) x)).symm

theorem absoluteConjugate_extensionDifference {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β γ : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L))
    (hγ : ∀ x : PerfectFieldClosure K, γ x = (α x : AlgebraicClosure L))
    (σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    absoluteConjugate α γ hγ σ = extensionDifference α β γ hβ hγ *
      absoluteConjugate α β hβ σ * (extensionDifference α β γ hβ hγ)⁻¹ := by
  ext x
  simp [AlgEquiv.mul_apply, extensionDifference, absoluteConjugate]
  change γ x = β (β.symm (γ x))
  exact (β.apply_symm_apply _).symm

theorem isomCOfExtension_eq (ell : ℕ) {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β γ : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L))
    (hγ : ∀ x : PerfectFieldClosure K, γ x = (α x : AlgebraicClosure L)) :
    isomCOfExtension ell α β hβ = isomCOfExtension ell α γ hγ := by
  apply Subtype.ext
  ext x
  obtain ⟨σ, rfl⟩ := absoluteToPiA_surjective ell L x
  change absoluteToPiA ell K (absoluteConjugate α β hβ σ) =
    absoluteToPiA ell K (absoluteConjugate α γ hγ σ)
  rw [absoluteConjugate_extensionDifference α β γ hβ hγ σ]
  let f : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* PiA ell K := absoluteToPiA ell K
  change f _ = f _
  simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]

end BogomolovPop

namespace BogomolovPop

def canonicalPullback (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) : IsomC ell K L :=
  isomCOfExtension ell α.1 (extendPerfectEquiv α.1) (extendPerfectEquiv_spec α.1)

theorem canonicalPullback_frobenius (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    {α χ : PerfectIsom k K l L} (h : FrobeniusStep α χ) :
    canonicalPullback ell α = canonicalPullback ell χ := by
  obtain ⟨p, hp, hpL, hχ⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  let : CharP L p := (CharP.charP_iff_prime_eq_zero hp).mpr hpL
  let β := extendPerfectEquiv α.1
  have hβ := extendPerfectEquiv_spec α.1
  let γ := β.trans (frobeniusEquiv (AlgebraicClosure L) p)
  have hγ : ∀ x : PerfectFieldClosure K, γ x = (χ.1 x : AlgebraicClosure L) := by
    intro x
    change (β x) ^ p = (χ.1 x : AlgebraicClosure L)
    rw [hβ, hχ x]
    rfl
  have heq : isomCOfExtension ell α.1 β hβ = isomCOfExtension ell χ.1 γ hγ := by
    apply Subtype.ext
    ext x
    obtain ⟨σ, rfl⟩ := absoluteToPiA_surjective ell L x
    change absoluteToPiA ell K (absoluteConjugate α.1 β hβ σ) =
      absoluteToPiA ell K (absoluteConjugate χ.1 γ hγ σ)
    congr 1
    apply AlgEquiv.ext
    intro x
    apply γ.injective
    let σ' : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L := σ
    change γ (β.symm (σ' (β x))) = γ (γ.symm (σ' (γ x)))
    rw [γ.apply_symm_apply]
    change (β (β.symm (σ' (β x)))) ^ p = σ' ((β x) ^ p)
    rw [β.apply_symm_apply, map_pow]
  exact heq.trans (isomCOfExtension_eq ell χ.1 γ (extendPerfectEquiv χ.1) hγ
    (extendPerfectEquiv_spec χ.1))

theorem canonicalPullback_eq_of_frobeniusOrbit (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    {α χ : PerfectIsom k K l L}
    (h : Relation.EqvGen (FrobeniusStep (k := k) (K := K) (l := l) (L := L)) α χ) :
    canonicalPullback ell α = canonicalPullback ell χ := by
  induction h with
  | rel a b hab => exact canonicalPullback_frobenius ell hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def canonicalPhi (ell : ℕ) [Fact ell.Prime] {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L] :
    IsomF k K l L → IsomCUnits ell K L :=
  Quotient.lift (fun α => Quotient.mk _ (canonicalPullback ell α)) (by
    intro α χ h
    rw [canonicalPullback_eq_of_frobeniusOrbit ell h])

end BogomolovPop

namespace BogomolovPop

end BogomolovPop

end
end

end OAI


