-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
-- name    : OAI_Probability_ThorpShuffle_Cyclic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:43:31.220794+00:00
-- url     : https://prove2.me/theorems/e24de474-13a1-4c1b-aba4-b7d0d538d885
-- title:
--   Irreducibility of cyclic subrepresentations via a rank-one operator, and alternators on permutation modules
-- statement:
--   Let $G$ be a group and $E$ a complex inner product space, with inner product $\langle\cdot,\cdot\rangle$ conjugate-linear in the first argument. Let $\rho$ be a representation of $G$ on $E$ by linear maps. A subrepresentation is a $G$-invariant linear subspace. For $e\in E$, the cyclic subrepresentation is $C(e)=\operatorname{span}_{\mathbb{C}}\{\rho(g)e: g\in G\}$; it contains $e$.
--
--   1. *Dichotomy.* Assume that $\rho$ is unitary, $\langle\rho(g)x,\rho(g)y\rangle=\langle x,y\rangle$ for all $g,x,y$. Let $K:E\to E$ be the linear map $Kv=\langle e,v\rangle\,e$, and assume that every subrepresentation $U$ satisfies $K(U)\subseteq U$. Then every subrepresentation $U$ satisfies $C(e)\subseteq U$ or $U\perp C(e)$, i.e. $\langle v,u\rangle=0$ for all $u\in U$, $v\in C(e)$.
--   2. *Irreducibility.* Under the same hypotheses and $e\ne0$, the representation of $G$ on $C(e)$ is irreducible: it is nonzero, and its only subrepresentations are $0$ and $C(e)$.
--
--   Now let $X$ be a finite set on which $G$ acts, and let $\mathbb{C}^X$ carry the standard inner product and the standard basis vectors $\delta_x$. The permutation representation is $(\pi(g)v)(x)=v(g^{-1}x)$. It is unitary and satisfies $\pi(g)\delta_x=\delta_{gx}$. Let $H$ be a finite group, $\iota:H\to G$ a group homomorphism and $\chi:H\to\mathbb{C}$ a multiplicative map ($\chi(1)=1$, $\chi(hh')=\chi(h)\chi(h')$). The alternator is the operator
--   $$
--   \mathcal A=\sum_{h\in H}\chi(h)\,\pi(\iota(h)),\qquad(\mathcal Av)(x)=\sum_{h\in H}\chi(h)\,v\bigl(\iota(h)^{-1}x\bigr).
--   $$
--
--   3. *Stability and translation.* Every subrepresentation of $\pi$ is mapped into itself by $\mathcal A$, and $\mathcal A\,\pi(\iota(a))v=\chi(a^{-1})\,\mathcal Av$ for $a\in H$.
--   4. *Vanishing.* If $\iota(a)x=x$ and $\chi(a)=-1$ for some $a\in H$, then $\mathcal A\delta_x=0$.
--   5. *Normalization.* If $\iota(h)b=b$ implies $h=1$, then $(\mathcal A\delta_b)(b)=1$.
--   6. *Inner products.* If $\chi$ is real-valued and $\chi(h^{-1})=\chi(h)$ for all $h$, then $\langle\mathcal A\delta_b,v\rangle=(\mathcal Av)(b)$.
--   7. *Rank one.* Assume that $\chi$ is real-valued with $\chi(h^{-1})=\chi(h)$, that $\iota(h)b=b$ implies $h=1$, and that every $x\in X$ is either fixed by some $\iota(a)$ with $\chi(a)=-1$ or lies in the orbit $\{\iota(a)b: a\in H\}$. Then, with $e_b=\mathcal A\delta_b$,
--   $$
--   \mathcal Av=\langle e_b,v\rangle\,e_b\qquad\text{for all }v\in\mathbb{C}^X .
--   $$
--
--   The permutation representation is unitary and $e_b\ne0$ by item 5. With these, items 3 and 7 supply the hypotheses of items 1 and 2 for $K=\mathcal A$ and $e=e_b$, which is the standard irreducibility argument for Specht modules. There $X$ is a set of tabloids, $H$ is a column group acting through the inclusion $\iota$, $\chi$ is the sign character, and $e_b$ is the polytabloid of the base tabloid. The Specht module is then the cyclic subrepresentation $C(e_b)$.
--
--   **Formalization Note** $C(e)$ is `Specht.cyclic ρ e`, $\mathbb{C}^X$ is `EuclideanSpace ℂ X` with the representation `PermutationSpace.rep`, and $\mathcal A$ is `PermutationSpace.alternator ι χ`, where `χ : H →* ℂ` is a monoid homomorphism into the multiplicative monoid of $\mathbb{C}$. The main results are `submodule_alternative`, `cyclic_irreducible` (irreducibility as `Representation.IsIrreducible`) and `alternator_rank_one`, and the remaining lemmas are the auxiliary facts listed above. No finite-dimensionality or completeness of $E$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/Cyclic.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/Cyclic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability

namespace OAI

universe uG uE uX uH

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Specht

variable {G : Type uG} [Group G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma self_mem_cyclic (ρ : Representation ℂ G E) (e : E) : e ∈ cyclic ρ e := by
  exact Submodule.subset_span ⟨1, by simp⟩

theorem submodule_alternative (ρ : Representation ℂ G E) (e : E)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (K : Module.End ℂ E) (hK : ∀ v, K v = ⟪e, v⟫_ℂ • e)
    (hstable : ∀ U : Subrepresentation ρ, ∀ v ∈ U, K v ∈ U)
    (U : Subrepresentation ρ) :
    cyclic ρ e ≤ U ∨ ∀ u ∈ U, ∀ v ∈ cyclic ρ e, ⟪v, u⟫_ℂ = 0 := by
  classical
  by_cases he : e ∈ U
  · left
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact U.apply_mem_toSubmodule g he)
  · right
    intro u hu v hv
    have horth (g : G) : ⟪ρ g e, u⟫_ℂ = 0 := by
      have hgu : ρ g⁻¹ u ∈ U := U.apply_mem_toSubmodule g⁻¹ hu
      have hk := hstable U _ hgu
      rw [hK] at hk
      have hz : ⟪e, ρ g⁻¹ u⟫_ℂ = 0 := by
        by_contra hne
        apply he
        have hh := U.toSubmodule.smul_mem (⟪e, ρ g⁻¹ u⟫_ℂ)⁻¹ hk
        change e ∈ U.toSubmodule
        simpa [smul_smul, hne] using hh
      have hi := hunit g e (ρ g⁻¹ u)
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] using hi.trans hz
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨g, rfl⟩ := hv; exact horth g
    | zero => simp
    | add x y hx hy ihx ihy => simp [ihx, ihy]
    | smul a x hx ih => simp [ih]

theorem cyclic_irreducible (ρ : Representation ℂ G E) (e : E) (he : e ≠ 0)
    (hunit : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (K : Module.End ℂ E) (hK : ∀ v, K v = ⟪e, v⟫_ℂ • e)
    (hstable : ∀ U : Subrepresentation ρ, ∀ v ∈ U, K v ∈ U) :
    Representation.IsIrreducible (cyclic ρ e).toRepresentation := by
  let S := cyclic ρ e
  let eS : S.toSubmodule := ⟨e, self_mem_cyclic ρ e⟩
  have heS : eS ≠ 0 := by intro hh; apply he; exact congrArg Subtype.val hh
  have htb : (⊤ : Subrepresentation S.toRepresentation) ≠ ⊥ := by
    intro hh
    have hel : eS ∈ (⊤ : Subrepresentation S.toRepresentation) := by trivial
    rw [hh] at hel
    exact heS hel
  let : Nontrivial (Subrepresentation S.toRepresentation) := ⟨⟨⊤, ⊥, htb⟩⟩
  refine ⟨fun U => ?_⟩
  let U' : Subrepresentation ρ := {
    toSubmodule := U.toSubmodule.map S.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨S.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩ }
  rcases submodule_alternative ρ e hunit K hK hstable U' with h | h
  · right
    apply top_unique
    intro u _
    obtain ⟨v, hv, heq⟩ := h u.property
    have hvu : v = u := Subtype.ext heq
    exact hvu ▸ hv
  · left
    apply bot_unique
    intro u hu
    have hum : (u : E) ∈ U' := ⟨u, hu, rfl⟩
    have hh := h _ hum _ u.property
    have hz : (u : E) = 0 := inner_self_eq_zero.mp hh
    exact Subtype.ext hz

namespace PermutationSpace
open scoped Classical

variable {X : Type uX} [Fintype X] [MulAction G X]

omit [Fintype X] in
@[simp] lemma rep_apply (g : G) (v : EuclideanSpace ℂ X) (x : X) :
    rep g v x = v (g⁻¹ • x) := rfl

lemma rep_unitary (g : G) (v w : EuclideanSpace ℂ X) :
    ⟪rep g v, rep g w⟫_ℂ = ⟪v, w⟫_ℂ := by
  simp only [PiLp.inner_apply, rep_apply]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun x => inner ℂ (v x) (w x))

omit [Fintype X] in
lemma rep_single (g : G) (x : X) :
    rep g (EuclideanSpace.single x (1 : ℂ)) = EuclideanSpace.single (g • x) (1 : ℂ) := by
  classical
  ext y
  simp only [rep_apply, PiLp.single_apply, inv_smul_eq_iff]

variable {H : Type uH} [Group H] [Fintype H]

omit [Fintype X] in
lemma alternator_apply (ι : H →* G) (χ : H →* ℂ) (v : EuclideanSpace ℂ X) :
    alternator ι χ v = ∑ h, χ h • rep (ι h) v := by
  simp [alternator, LinearMap.sum_apply]

omit [Fintype X] in
lemma alternator_stable (ι : H →* G) (χ : H →* ℂ)
    (U : Subrepresentation (rep : Representation ℂ G (EuclideanSpace ℂ X)))
    (v : EuclideanSpace ℂ X) (hv : v ∈ U) : alternator ι χ v ∈ U := by
  rw [alternator_apply]
  exact U.toSubmodule.sum_mem fun h _ => U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule _ hv)

omit [Fintype X] in
lemma alternator_translate (ι : H →* G) (χ : H →* ℂ) (a : H)
    (v : EuclideanSpace ℂ X) :
    alternator ι χ (rep (ι a) v) = χ a⁻¹ • alternator ι χ v := by
  rw [alternator_apply, alternator_apply, Finset.smul_sum]
  have he := Equiv.sum_comp (Equiv.mulRight a)
    (fun h => χ a⁻¹ • (χ h • (rep (ι h) v : EuclideanSpace ℂ X)))
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulRight, smul_smul, map_mul]
  rw [show χ a⁻¹ * (χ h * χ a) = χ h by
    calc
      _ = χ h * (χ a⁻¹ * χ a) := by ring
      _ = χ h := by rw [← map_mul, inv_mul_cancel, map_one, mul_one]]
  simp only [Module.End.mul_apply]

omit [Fintype X] in
lemma alternator_single_zero (ι : H →* G) (χ : H →* ℂ)
    (x : X) (a : H) (ha : ι a • x = x) (hs : χ a = -1) :
    alternator ι χ (EuclideanSpace.single x (1 : ℂ)) = 0 := by
  have hh := alternator_translate ι χ a (EuclideanSpace.single x (1 : ℂ))
  rw [rep_single, ha, map_inv, hs, inv_neg, inv_one, neg_smul, one_smul] at hh
  have hz := congrArg (fun z => z + alternator ι χ (EuclideanSpace.single x (1 : ℂ))) hh
  have ht : (2 : ℂ) • alternator ι χ (EuclideanSpace.single x (1 : ℂ)) = 0 := by
    simpa [two_smul] using hz
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

omit [Fintype X] in
lemma alternator_coeff (ι : H →* G) (χ : H →* ℂ) (v : EuclideanSpace ℂ X) (x : X) :
    alternator ι χ v x = ∑ h, χ h * v ((ι h)⁻¹ • x) := by
  simp [alternator_apply, WithLp.ofLp_sum, Finset.sum_apply]

omit [Fintype X] in
lemma polytabloid_base (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hfree : ∀ h : H, ι h • b = b → h = 1) :
    alternator ι χ (EuclideanSpace.single b (1 : ℂ)) b = 1 := by
  classical
  rw [alternator_coeff, Finset.sum_eq_single 1]
  · simp
  · intro h _ hh
    have hn : (ι h)⁻¹ • b ≠ b := by
      intro he
      have hi : h⁻¹ = 1 := hfree h⁻¹ (by simpa using he)
      exact hh (inv_eq_one.mp hi)
    simp [hn]
  · simp

lemma polytabloid_inner (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hreal : ∀ h, conj (χ h) = χ h) (hinv : ∀ h, χ h⁻¹ = χ h)
    (v : EuclideanSpace ℂ X) :
    ⟪alternator ι χ (EuclideanSpace.single b (1 : ℂ)), v⟫_ℂ = alternator ι χ v b := by
  classical
  rw [alternator_apply, sum_inner, alternator_coeff]
  simp only [inner_smul_left, rep_single, EuclideanSpace.inner_single_left, map_one,
    one_mul, hreal]
  have hh := Equiv.sum_comp (Equiv.inv H) (fun h => χ h * v ((ι h)⁻¹ • b))
  simpa only [Equiv.inv_apply, map_inv, inv_inv, hinv] using hh

theorem alternator_rank_one (ι : H →* G) (χ : H →* ℂ) (b : X)
    (hreal : ∀ h, conj (χ h) = χ h) (hinv : ∀ h, χ h⁻¹ = χ h)
    (hfree : ∀ h : H, ι h • b = b → h = 1)
    (halt : ∀ x : X, (∃ a : H, ι a • x = x ∧ χ a = -1) ∨
      ∃ a : H, x = ι a • b) (v : EuclideanSpace ℂ X) :
    alternator ι χ v =
      ⟪alternator ι χ (EuclideanSpace.single b (1 : ℂ)), v⟫_ℂ •
        alternator ι χ (EuclideanSpace.single b (1 : ℂ)) := by
  classical
  let e := alternator ι χ (EuclideanSpace.single b (1 : ℂ))
  have hs (x : X) : alternator ι χ (EuclideanSpace.single x (1 : ℂ)) ∈ Submodule.span ℂ {e} := by
    rcases halt x with ⟨a, ha, hχ⟩ | ⟨a, rfl⟩
    · rw [alternator_single_zero ι χ x a ha hχ]
      exact Submodule.zero_mem _
    · rw [← rep_single, alternator_translate]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e))
  have hv : alternator ι χ v ∈ Submodule.span ℂ {e} := by
    have hexp := (EuclideanSpace.basisFun X ℂ).sum_repr v
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hexp
    rw [← hexp, map_sum]
    exact Submodule.sum_mem _ fun x _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hs x)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
  have heb : e b = 1 := polytabloid_base ι χ b hfree
  have hab : a = alternator ι χ v b := by
    have hh := congrArg (fun z : EuclideanSpace ℂ X => z b) ha
    simpa only [PiLp.smul_apply, smul_eq_mul, heb, mul_one] using hh
  rw [← ha, hab, polytabloid_inner ι χ b hreal hinv]

end PermutationSpace

end Thorp.Specht

end

end OAI


