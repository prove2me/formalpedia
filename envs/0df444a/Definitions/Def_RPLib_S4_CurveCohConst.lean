-- Prove2me | Definitions.Def_RPLib_S4_CurveCohConst
-- name    : RPLib_S4_CurveCohConst
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:04:12.855898+00:00
-- url     : https://prove2.me/theorems/ee4fd6cf-cb43-4a8b-8435-44aaf8ec48e0
-- title:
--   Compactly supported $H^1$ with constant coefficients
-- statement:
--   In the setting of cohomology of a group relative to a family of inertia subgroups $(I_s)_{s \in S}$, the file derives from the exact sequence $0 \to H^0 \to \bigoplus_s M^{I_s} \to H^1_c \to H^1_{par} \to 0$ that $(\bigoplus_s M^{I_s})/H^0$ embeds in $H^1_c$, with equality when $H^1_{par} = 0$. For constant coefficients ($\Gamma$ acting trivially on $M$, e.g. $M = \mathbb{Z}/\ell^n$) it proves $H^0 = M$, $H^2_c = M$, $M^{S \setminus \{s_0\}} \hookrightarrow H^1_c$, and $$H^1_c \cong M^{S \setminus \{s_0\}} \quad \text{when } H^1_{par} = 0,$$ so for $M = \Lambda$ free the group $H^1_c$ is free of rank $\#S - 1$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Galois Cohomology, Springer (1997), Chapter I, Section 2; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5 and Chapter V, Section 2

import Definitions.Def_RPLib_S4_CurveCohPair

/-!
# S4-CurveCoh, part 1b: consequences of the exact sequence, and constant coefficients

* `(⊕_s M^{I_s}) / H⁰ ↪ H¹_c` (exactness), and it is an isomorphism when `H¹_par = 0`;
* constant coefficients (`Γ` acts trivially, e.g. the constant sheaf `Λ = ℤ/lⁿ` or `O/λⁿ` on `U_j`):
  `H⁰ = M`, `H²_c = M` (before the Tate twist), `M^{S ∖ {s₀}} ↪ H¹_c`, and `H¹_c ≅ M^{S ∖ {s₀}}` when `H¹_par = 0`
  (for `U ⊆ ℙ¹`, `H¹_par = H¹(ℙ¹) = 0` is supplied by S4-Kummer); for `M = Λ` this is free of rank `#S - 1`.
Everything is over an arbitrary commutative ring `k` (review END-2, decision R19).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

set_option linter.unusedSectionVars false

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G)
  {S : Type} (I : S → Subgroup G)

theorem ker_bdryToH1c : LinearMap.ker (bdryToH1c ρ Γ I) = LinearMap.range (h0ToBdry ρ Γ I) :=
  LinearMap.exact_iff.mp (exact_h0ToBdry_bdryToH1c ρ Γ I)

/-- `(⊕_s M^{I_s}) / H⁰ → H¹_c`. -/
noncomputable def bdryQuotToH1c : (bdryInv ρ Γ I ⧸ LinearMap.range (h0ToBdry ρ Γ I)) →ₗ[k] H1c ρ Γ I :=
  (LinearMap.range (h0ToBdry ρ Γ I)).liftQ (bdryToH1c ρ Γ I) (ker_bdryToH1c ρ Γ I).ge

theorem bdryQuotToH1c_mk (b : bdryInv ρ Γ I) :
    bdryQuotToH1c ρ Γ I (Submodule.Quotient.mk b) = bdryToH1c ρ Γ I b := rfl

theorem bdryQuotToH1c_injective : Function.Injective (bdryQuotToH1c ρ Γ I) := by
  rw [← LinearMap.ker_eq_bot, bdryQuotToH1c, Submodule.ker_liftQ, ker_bdryToH1c, Submodule.mkQ_map_self]

theorem bdryToH1c_surjective (hpar : H1par ρ Γ I = ⊥) : Function.Surjective (bdryToH1c ρ Γ I) := by
  intro x
  have hx : h1cToH1 ρ Γ I x = 0 := by
    have h : h1cToH1 ρ Γ I x ∈ H1par ρ Γ I := range_h1cToH1 ρ Γ I ▸ LinearMap.mem_range_self _ x
    rw [hpar] at h
    exact (Submodule.mem_bot k).1 h
  exact (exact_bdryToH1c_h1cToH1 ρ Γ I x).1 hx

/-- If `H¹_par = 0` then `H¹_c ≅ (⊕_s M^{I_s}) / H⁰`. -/
noncomputable def bdryQuotEquivH1c (hpar : H1par ρ Γ I = ⊥) :
    (bdryInv ρ Γ I ⧸ LinearMap.range (h0ToBdry ρ Γ I)) ≃ₗ[k] H1c ρ Γ I :=
  LinearEquiv.ofBijective (bdryQuotToH1c ρ Γ I)
    ⟨bdryQuotToH1c_injective ρ Γ I, by
      intro x
      obtain ⟨b, rfl⟩ := bdryToH1c_surjective ρ Γ I hpar x
      exact ⟨Submodule.Quotient.mk b, rfl⟩⟩

/-! ## Constant coefficients -/

section Constant

/-- Constant coefficients: `H⁰ = M`. -/
noncomputable def h0ConstEquiv (htriv : ∀ g : Γ, ρ g = 1) : H0 ρ Γ ≃ₗ[k] M :=
  (LinearEquiv.ofEq _ _ (H0_eq_top_of_trivial ρ Γ htriv)).trans (LinearEquiv.ofTop ⊤ rfl)

theorem coinvariantsKer_eq_bot (htriv : ∀ g : Γ, ρ g = 1) :
    Representation.Coinvariants.ker (ρ.comp Γ.subtype) = ⊥ := by
  rw [Representation.Coinvariants.ker, Submodule.span_eq_bot]
  rintro _ ⟨⟨g, x⟩, rfl⟩
  show ρ (g : G) x - x = 0
  rw [htriv g, Module.End.one_apply, sub_self]

/-- Constant coefficients: `H²_c = M_Γ = M` (the Tate twist `(-1)` lives in the Frobenius, see `frobH2c`). -/
noncomputable def h2cConstEquiv (htriv : ∀ g : Γ, ρ g = 1) : H2c ρ Γ ≃ₗ[k] M :=
  Submodule.quotEquivOfEqBot _ (coinvariantsKer_eq_bot ρ Γ htriv)

variable (s0 : S)

/-- `b ↦ (b_s - b_{s₀})_{s ≠ s₀}`. -/
def bdryDiff : bdryInv ρ Γ I →ₗ[k] ({s // s ≠ s0} → M) where
  toFun b s := (b : S → M) s - (b : S → M) s0
  map_add' b b' := by
    funext s
    simp only [Submodule.coe_add, Pi.add_apply]
    abel
  map_smul' a b := by
    funext s
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_sub, RingHom.id_apply]

theorem bdryDiff_apply (b : bdryInv ρ Γ I) (s : {s // s ≠ s0}) :
    bdryDiff ρ Γ I s0 b s = (b : S → M) s - (b : S → M) s0 := rfl

theorem ker_bdryDiff (htriv : ∀ g : Γ, ρ g = 1) :
    LinearMap.ker (bdryDiff ρ Γ I s0) = LinearMap.range (h0ToBdry ρ Γ I) := by
  ext b
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hb
    refine ⟨⟨(b : S → M) s0, by rw [H0_eq_top_of_trivial ρ Γ htriv]; trivial⟩, ?_⟩
    apply Subtype.ext
    funext s
    by_cases hs : s = s0
    · subst hs
      rfl
    · have h := congrFun hb ⟨s, hs⟩
      rw [bdryDiff_apply, Pi.zero_apply, sub_eq_zero] at h
      exact h.symm
  · rintro ⟨m, rfl⟩
    funext s
    exact sub_self _

theorem bdryDiff_surjective (htriv : ∀ g : Γ, ρ g = 1) : Function.Surjective (bdryDiff ρ Γ I s0) := by
  classical
  intro f
  refine ⟨⟨fun s => if h : s = s0 then 0 else f ⟨s, h⟩, by
    rw [bdryInv_eq_top_of_trivial ρ Γ I htriv]; trivial⟩, ?_⟩
  funext s
  rw [bdryDiff_apply]
  simp [s.2]

/-- Constant coefficients: `M^{S ∖ {s₀}} ≅ (⊕_s M) / M`. -/
noncomputable def constQuotEquiv (htriv : ∀ g : Γ, ρ g = 1) :
    (bdryInv ρ Γ I ⧸ LinearMap.range (h0ToBdry ρ Γ I)) ≃ₗ[k] ({s // s ≠ s0} → M) :=
  (Submodule.quotEquivOfEq _ _ (ker_bdryDiff ρ Γ I s0 htriv).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (bdryDiff_surjective ρ Γ I s0 htriv))

/-- Constant coefficients: `M^{S ∖ {s₀}} ↪ H¹_c` (the classes of the boundary trivialisations). -/
noncomputable def constToH1c (htriv : ∀ g : Γ, ρ g = 1) : ({s // s ≠ s0} → M) →ₗ[k] H1c ρ Γ I :=
  bdryQuotToH1c ρ Γ I ∘ₗ (constQuotEquiv ρ Γ I s0 htriv).symm.toLinearMap

theorem constToH1c_injective (htriv : ∀ g : Γ, ρ g = 1) : Function.Injective (constToH1c ρ Γ I s0 htriv) :=
  (bdryQuotToH1c_injective ρ Γ I).comp (constQuotEquiv ρ Γ I s0 htriv).symm.injective

/-- Constant coefficients and `H¹_par = 0` (e.g. `U_j ⊆ ℙ¹`): `H¹_c ≅ M^{S ∖ {s₀}}`. -/
noncomputable def h1cConstEquiv (htriv : ∀ g : Γ, ρ g = 1) (hpar : H1par ρ Γ I = ⊥) :
    H1c ρ Γ I ≃ₗ[k] ({s // s ≠ s0} → M) :=
  (bdryQuotEquivH1c ρ Γ I hpar).symm.trans (constQuotEquiv ρ Γ I s0 htriv)

/-- The constant sheaf `Λ`: `H¹_c` is free over `Λ`. -/
theorem free_H1c_const (ρ' : Representation k G k) [Finite S] [Nonempty S] (htriv : ∀ g : Γ, ρ' g = 1)
    (hpar : H1par ρ' Γ I = ⊥) : Module.Free k (H1c ρ' Γ I) :=
  Module.Free.of_equiv (h1cConstEquiv ρ' Γ I (Classical.arbitrary S) htriv hpar).symm

/-- The constant sheaf `Λ` (`Λ ≠ 0`): `H¹_c` has rank `#S - 1` (the sanity check of the unit goal). -/
theorem finrank_H1c_const [Nontrivial k] (ρ' : Representation k G k) [Fintype S] [DecidableEq S]
    [Nonempty S] (htriv : ∀ g : Γ, ρ' g = 1) (hpar : H1par ρ' Γ I = ⊥) :
    Module.finrank k (H1c ρ' Γ I) = Fintype.card S - 1 := by
  rw [(h1cConstEquiv ρ' Γ I (Classical.arbitrary S) htriv hpar).finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp [Fintype.card_subtype_compl]

end Constant

end

end CurveCoh
end RamanujanPetersson


