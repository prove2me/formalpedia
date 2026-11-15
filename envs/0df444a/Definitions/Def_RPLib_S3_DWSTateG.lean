-- Prove2me | Definitions.Def_RPLib_S3_DWSTateG
-- name    : RPLib_S3_DWSTateG
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:29:58.913586+00:00
-- url     : https://prove2.me/theorems/eca7bd78-343b-4b18-8c0a-01e3e9811648
-- title:
--   Weight-two Ramanujan-Petersson library: `F_q`-isomorphisms of quotients (b5, b6, b8)
-- statement:
--   `F_q`-isomorphisms of quotients (b5, b6, b8).
--
--   * `IsoFq W₁ W₂ L` : mutually inverse `F_q`-isogenies (`IsoFq.refl`, `IsoFq.symm`, `IsoFq.trans`).
--   * `isQuot_bot` (`id : E → E` is the quotient by `0`), `IsQuot.comp_endo` (precomposing a quotient by `G` with an
--     endomorphism `γ` with `γ γ' = γ' γ = [m]`, `p ∤ m`, gives the quotient by `γ⁻¹ G`), `isoFq_of_isQuot` (two
--     quotients by the same subgroup are `F_q`-isomorphic).
--   * `kerI_span`, `kerI_span_mul` (`E[(α) I] = ι(α)⁻¹ E[I]`), `kerI_top`.
--   * (b5) `isoFq_of_principal` : `E/E[(α)] ≅ E` (`α α' = N`, `p ∤ N`).
--   * (b6) `isoFq_of_span_mul_eq` : `(α) I = (β) J` ⇒ `E/E[I] ≅ E/E[J]`.
--   * (b8) `span_mul_eq_of_isoFq` : `E/E[I] ≅ E/E[J]` ⇒ `(c) J = (n) I` with `c ≠ 0`; `principal_of_isoFq`
--     (`E/E[I] ≅ E` ⇒ `I` principal).
--   * `quotOAct` : the `R`-structure `ι_I` on `E/E[I]` (so quotients can be iterated).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateF

/-!
# S3-DWS-Tate, part G: `F_q`-isomorphisms of quotients (b5, b6, b8)

* `IsoFq W₁ W₂ L` : mutually inverse `F_q`-isogenies (`IsoFq.refl`, `IsoFq.symm`, `IsoFq.trans`).
* `isQuot_bot` (`id : E → E` is the quotient by `0`), `IsQuot.comp_endo` (precomposing a quotient by `G` with an
  endomorphism `γ` with `γ γ' = γ' γ = [m]`, `p ∤ m`, gives the quotient by `γ⁻¹ G`), `isoFq_of_isQuot` (two
  quotients by the same subgroup are `F_q`-isomorphic).
* `kerI_span`, `kerI_span_mul` (`E[(α) I] = ι(α)⁻¹ E[I]`), `kerI_top`.
* (b5) `isoFq_of_principal` : `E/E[(α)] ≅ E` (`α α' = N`, `p ∤ N`).
* (b6) `isoFq_of_span_mul_eq` : `(α) I = (β) J` ⇒ `E/E[I] ≅ E/E[J]`.
* (b8) `span_mul_eq_of_isoFq` : `E/E[I] ≅ E/E[J]` ⇒ `(c) J = (n) I` with `c ≠ 0`; `principal_of_isoFq`
  (`E/E[I] ≅ E` ⇒ `I` principal).
* `quotOAct` : the `R`-structure `ι_I` on `E/E[I]` (so quotients can be iterated).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section IsoDef

variable {F : Type*} [Field F] [Fintype F]

attribute [local instance] finite_coordinateRing decEqFF

/-- `E₁ ≅ E₂` over `F_q`: mutually inverse isogenies commuting with Frobenius. -/
def IsoFq (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] (L : Type*) [Field L] [Algebra F L]
    [IsAlgClosed L] [DecidableEq L] : Prop :=
  ∃ u : Pt W₁ L →+ Pt W₂ L, ∃ v : Pt W₂ L →+ Pt W₁ L, IsIsog u ∧ IsIsog v ∧ (∀ P, v (u P) = P) ∧
    (∀ Q, u (v Q) = Q) ∧ ∀ P, u (RPLib.EllFq.frob W₁ L P) = RPLib.EllFq.frob W₂ L (u P)

end IsoDef

section Iso

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W W₁ W₂ W₃ : WeierstrassCurve F} [W.IsElliptic] [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

lemma isIsog_id : IsIsog (AddMonoidHom.id (Pt W L)) := by
  obtain ⟨Φ, hΦ⟩ := (mem_endRing (W := W) (L := L)).mp (endRing W L).one_mem
  exact ⟨Φ, fun S => hΦ S⟩

lemma isIsog_of_mem {γ : AddMonoid.End (Pt W L)} (hγ : γ ∈ endFq W L) :
    IsIsog (γ : Pt W L →+ Pt W L) := by
  obtain ⟨Γ, hΓ⟩ := (mem_endRing).mp (mem_endFq.mp hγ).1
  exact ⟨Γ, fun S => hΓ S⟩

lemma endFq_frob {γ : AddMonoid.End (Pt W L)} (hγ : γ ∈ endFq W L) (P : Pt W L) :
    γ (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W L (γ P) :=
  (DFunLike.congr_fun (mem_endFq.mp hγ).2 P).symm

lemma mem_endFq_of_isog {ε : Pt W L →+ Pt W L} (h : IsIsog ε)
    (hf : ∀ P, ε (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W L (ε P)) :
    (ε : AddMonoid.End (Pt W L)) ∈ endFq W L := by
  obtain ⟨E, hE⟩ := h
  exact mem_endFq.mpr ⟨(mem_endRing).mpr ⟨E, fun S => hE S⟩, AddMonoidHom.ext fun P => (hf P).symm⟩

lemma frob_inv {u : Pt W₁ L →+ Pt W₂ L} {v : Pt W₂ L →+ Pt W₁ L} (hvu : ∀ P, v (u P) = P)
    (huv : ∀ Q, u (v Q) = Q) (hf : ∀ P, u (RPLib.EllFq.frob W₁ L P) = RPLib.EllFq.frob W₂ L (u P))
    (Q : Pt W₂ L) : v (RPLib.EllFq.frob W₂ L Q) = RPLib.EllFq.frob W₁ L (v Q) := by
  have h1 := congrArg v (hf (v Q))
  rw [huv, hvu] at h1
  exact h1.symm

lemma IsoFq.refl : IsoFq W W L :=
  ⟨AddMonoidHom.id _, AddMonoidHom.id _, isIsog_id, isIsog_id, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

lemma IsoFq.symm (h : IsoFq W₁ W₂ L) : IsoFq W₂ W₁ L := by
  obtain ⟨u, v, hu, hv, hvu, huv, hf⟩ := h
  exact ⟨v, u, hv, hu, huv, hvu, frob_inv hvu huv hf⟩

lemma IsoFq.trans (h₁ : IsoFq W₁ W₂ L) (h₂ : IsoFq W₂ W₃ L) : IsoFq W₁ W₃ L := by
  obtain ⟨u₁, v₁, hu₁, hv₁, hvu₁, huv₁, hf₁⟩ := h₁
  obtain ⟨u₂, v₂, hu₂, hv₂, hvu₂, huv₂, hf₂⟩ := h₂
  refine ⟨u₂.comp u₁, v₁.comp v₂, hu₂.comp hu₁, hv₁.comp hv₂, fun P => ?_, fun Q => ?_, fun P => ?_⟩
  · simp only [AddMonoidHom.comp_apply, hvu₂, hvu₁]
  · simp only [AddMonoidHom.comp_apply, huv₁, huv₂]
  · simp only [AddMonoidHom.comp_apply, hf₁, hf₂]

/-- The identity is the quotient by `0`. -/
lemma isQuot_bot : IsQuot (⊥ : AddSubgroup (Pt W L)) (AddMonoidHom.id _) (AddMonoidHom.id _) 1 :=
  ⟨by rw [Nat.cast_one]; exact one_ne_zero, isIsog_id, isIsog_id, fun _ => AddSubgroup.mem_bot.symm,
    fun Q => ⟨Q, rfl⟩, fun P => (one_nsmul P).symm, fun Q => (one_nsmul Q).symm, fun _ => rfl, fun _ => rfl⟩

variable {G : AddSubgroup (Pt W L)} {φ : Pt W L →+ Pt W₁ L} {ψ : Pt W₁ L →+ Pt W L} {n : ℕ}
  {φ₂ : Pt W L →+ Pt W₂ L} {ψ₂ : Pt W₂ L →+ Pt W L} {n₂ : ℕ}

/-- Precomposing a quotient by `G` with an endomorphism `γ` (`γ γ' = γ' γ = [m]`, `p ∤ m`) gives the quotient by
`γ⁻¹ G`. -/
theorem IsQuot.comp_endo (hq : IsQuot G φ ψ n) {γ γ' : AddMonoid.End (Pt W L)} (hγ : γ ∈ endFq W L)
    (hγ' : γ' ∈ endFq W L) {m : ℕ} (hm : (m : F) ≠ 0) (h1 : ∀ P, γ (γ' P) = m • P)
    (h2 : ∀ P, γ' (γ P) = m • P) :
    IsQuot (G.comap γ) (φ.comp (γ : Pt W L →+ Pt W L)) ((γ' : Pt W L →+ Pt W L).comp ψ) (m * n) := by
  have hmL : (m : L) ≠ 0 := fun h => hm (by
    apply (algebraMap F L).injective; rw [map_natCast, h, map_zero])
  obtain ⟨A, hA⟩ := hq.isog
  obtain ⟨Γ, hΓ⟩ := (mem_endRing).mp (mem_endFq.mp hγ).1
  refine ⟨?_, HasGenI.comp_endo hA hΓ, (isIsog_of_mem hγ').comp hq.isogψ, fun S => ?_, fun Q => ?_,
    fun P => ?_, fun Q => ?_, fun P => ?_, fun Q => ?_⟩
  · rw [Nat.cast_mul]; exact mul_ne_zero hm hq.hn
  · exact hq.ker (γ S)
  · obtain ⟨P, rfl⟩ := hq.surj Q
    obtain ⟨T, rfl⟩ := nsmul_surjective (W := W) hmL P
    refine ⟨γ' T, ?_⟩
    show φ (γ (γ' T)) = φ (m • T)
    rw [h1]
  · show γ' (ψ (φ (γ P))) = (m * n) • P
    rw [hq.dual1, map_nsmul, h2, smul_smul, mul_comm]
  · show φ (γ (γ' (ψ Q))) = (m * n) • Q
    rw [h1, map_nsmul, hq.dual2, smul_smul]
  · show φ (γ (RPLib.EllFq.frob W L P)) = RPLib.EllFq.frob W₁ L (φ (γ P))
    rw [endFq_frob hγ, hq.frob]
  · show γ' (ψ (RPLib.EllFq.frob W₁ L Q)) = RPLib.EllFq.frob W L (γ' (ψ Q))
    rw [hq.frobψ, endFq_frob hγ']

/-- Two quotients of `E` by the same subgroup are `F_q`-isomorphic. -/
theorem isoFq_of_isQuot (hq₁ : IsQuot G φ ψ n) (hq₂ : IsQuot G φ₂ ψ₂ n₂) : IsoFq W₁ W₂ L := by
  obtain ⟨u, hu, huφ, huf⟩ := hq₁.factor hq₂.isog fun T hT => (hq₂.ker T).mpr hT
  obtain ⟨v, hv, hvφ, -⟩ := hq₂.factor hq₁.isog fun T hT => (hq₁.ker T).mpr hT
  refine ⟨u, v, hu, hv, fun P => ?_, fun Q => ?_, huf hq₂.frob⟩
  · obtain ⟨R, rfl⟩ := hq₁.surj P
    rw [huφ, hvφ]
  · obtain ⟨R, rfl⟩ := hq₂.surj Q
    rw [hvφ, huφ]

/-- Two quotients of `E` by equal subgroups are `F_q`-isomorphic. -/
theorem isoFq_of_isQuot' {G₁ G₂ : AddSubgroup (Pt W L)} (hG : G₁ = G₂) (hq₁ : IsQuot G₁ φ ψ n)
    (hq₂ : IsQuot G₂ φ₂ ψ₂ n₂) : IsoFq W₁ W₂ L := by
  subst hG
  exact isoFq_of_isQuot hq₁ hq₂

/-! ### Kernel ideals of principal ideals and products -/

variable {R : Type*} [CommRing R]

lemma OAct.apply_apply_eq (s : OAct R W L) {α α' : R} {N : ℕ} (h : α * α' = N) (P : Pt W L) :
    s.ι α (s.ι α' P) = N • P := by
  rw [← s.natCast_apply, ← h, map_mul]; rfl

lemma OAct.apply_apply_eq' (s : OAct R W L) {α α' : R} {N : ℕ} (h : α * α' = N) (P : Pt W L) :
    s.ι α' (s.ι α P) = N • P := by
  rw [s.ι_comm]; exact s.apply_apply_eq h P

lemma kerI_top (s : OAct R W L) : kerI s (⊤ : Ideal R) = ⊥ := by
  ext P
  rw [mem_kerI, AddSubgroup.mem_bot]
  constructor
  · intro h
    have h1 := h 1 Submodule.mem_top
    rw [map_one] at h1
    exact h1
  · rintro rfl α -
    exact map_zero _

lemma kerI_span (s : OAct R W L) (α : R) :
    kerI s (Ideal.span {α}) = (⊥ : AddSubgroup (Pt W L)).comap (s.ι α) := by
  ext P
  show P ∈ kerI s (Ideal.span {α}) ↔ s.ι α P ∈ (⊥ : AddSubgroup (Pt W L))
  rw [AddSubgroup.mem_bot, mem_kerI]
  constructor
  · intro h
    exact h α (Ideal.mem_span_singleton_self α)
  · intro h β hβ
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hβ
    have h' : s.ι α P = 0 := h
    rw [map_mul]
    show s.ι c (s.ι α P) = 0
    rw [h', map_zero]

/-- `E[(α) I] = ι(α)⁻¹ E[I]`. -/
lemma kerI_span_mul (s : OAct R W L) (α : R) (I : Ideal R) :
    kerI s (Ideal.span {α} * I) = (kerI s I).comap (s.ι α) := by
  ext P
  show P ∈ kerI s (Ideal.span {α} * I) ↔ s.ι α P ∈ kerI s I
  rw [mem_kerI, mem_kerI]
  constructor
  · intro h β hβ
    have h1 := h (α * β) (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self α) hβ)
    rw [map_mul] at h1
    show s.ι β (s.ι α P) = 0
    rw [s.ι_comm]
    exact h1
  · intro h x hx
    obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.mp hx
    have h1 : s.ι z (s.ι α P) = 0 := h z hz
    rw [map_mul]
    show s.ι α (s.ι z P) = 0
    rw [s.ι_comm]
    exact h1

/-- **(b5)** `E/E[(α)] ≅ E` when `α α' = N` with `p ∤ N`. -/
theorem isoFq_of_principal (s : OAct R W L) {α α' : R} {N : ℕ} (hαα' : α * α' = N) (hNF : (N : F) ≠ 0)
    (hq : IsQuot (kerI s (Ideal.span {α})) φ ψ n) : IsoFq W₁ W L := by
  have hq' := (isQuot_bot (W := W) (L := L)).comp_endo (s.mem α) (s.mem α') hNF
    (s.apply_apply_eq hαα') (s.apply_apply_eq' hαα')
  exact isoFq_of_isQuot' (kerI_span s α) hq hq'

/-- **(b6)** `(α) I = (β) J` ⇒ `E/E[I] ≅ E/E[J]` (`α α' = M`, `β β' = N`, `p ∤ M N`). -/
theorem isoFq_of_span_mul_eq (s : OAct R W L) {I J : Ideal R} (hq₁ : IsQuot (kerI s I) φ ψ n)
    (hq₂ : IsQuot (kerI s J) φ₂ ψ₂ n₂) {α α' β β' : R} {M N : ℕ} (hα : α * α' = M) (hM : (M : F) ≠ 0)
    (hβ : β * β' = N) (hN : (N : F) ≠ 0) (h : Ideal.span {α} * I = Ideal.span {β} * J) :
    IsoFq W₁ W₂ L := by
  have e₁ := hq₁.comp_endo (s.mem α) (s.mem α') hM (s.apply_apply_eq hα) (s.apply_apply_eq' hα)
  have e₂ := hq₂.comp_endo (s.mem β) (s.mem β') hN (s.apply_apply_eq hβ) (s.apply_apply_eq' hβ)
  exact isoFq_of_isQuot' ((kerI_span_mul s α I).symm.trans ((congrArg (kerI s) h).trans (kerI_span_mul s β J)))
    e₁ e₂

/-- One half of (b8): an `F_q`-isogeny `u : E/E[I] → E/E[J]` gives `c` (with `ι(c) = ψ_J u φ_I`) and
`J c ⊆ n_J I`. -/
theorem exists_mul_eq_of_isog [IsDomain R] (s : OAct R W L) {I I' J : Ideal R} {NI : ℕ}
    (hI : I * I' = Ideal.span {(NI : R)}) (hNI : (NI : F) ≠ 0)
    (hq₁ : IsQuot (kerI s I) φ ψ n) (hq₂ : IsQuot (kerI s J) φ₂ ψ₂ n₂)
    {u : Pt W₁ L →+ Pt W₂ L} (hu : IsIsog u)
    (huf : ∀ P, u (RPLib.EllFq.frob W₁ L P) = RPLib.EllFq.frob W₂ L (u P)) :
    ∃ c : R, (∀ P, s.ι c P = ψ₂ (u (φ P))) ∧ ∀ j ∈ J, ∃ i ∈ I, j * c = (n₂ : R) * i := by
  obtain ⟨c, hc⟩ := s.surj _ (mem_endFq_of_isog ((hq₂.isogψ.comp hu).comp hq₁.isog) fun P => by
    show ψ₂ (u (φ (RPLib.EllFq.frob W L P))) = RPLib.EllFq.frob W L (ψ₂ (u (φ P)))
    rw [hq₁.frob, huf, hq₂.frobψ])
  have hcP : ∀ P, s.ι c P = ψ₂ (u (φ P)) := fun P => by rw [hc]; rfl
  refine ⟨c, hcP, fun j hj => ?_⟩
  obtain ⟨j', hj', hj'φ, hj'f⟩ := hq₂.factor (W₁ := W) (α := (s.ι j : Pt W L →+ Pt W L))
    (isIsog_of_mem (s.mem j)) (fun T hT => mem_kerI.mp hT j hj)
  have hj'fr := hj'f (s.frob_comm j)
  have hjP : ∀ P, s.ι j P = j' (φ₂ P) := fun P => (hj'φ P).symm
  obtain ⟨i, hi⟩ := s.surj _ (mem_endFq_of_isog ((hj'.comp hu).comp hq₁.isog) fun P => by
    show j' (u (φ (RPLib.EllFq.frob W L P))) = RPLib.EllFq.frob W L (j' (u (φ P)))
    rw [hq₁.frob, huf, hj'fr])
  have hiP : ∀ P, s.ι i P = j' (u (φ P)) := fun P => by rw [hi]; rfl
  have hiI : i ∈ I := mem_of_kills_kerI (s := s) hI hNI fun P hP => by
    rw [hiP, (hq₁.ker P).mpr hP, map_zero, map_zero]
  refine ⟨i, hiI, s.inj (AddMonoidHom.ext fun P => ?_)⟩
  rw [map_mul, map_mul]
  show s.ι j (s.ι c P) = s.ι (n₂ : R) (s.ι i P)
  rw [hcP, hjP, hq₂.dual2, s.natCast_apply, map_nsmul, hiP]

/-- **(b8)** `E/E[I] ≅ E/E[J]` ⇒ `(c) J = (n_J) I` for some `c ≠ 0` (`I I' = (N_I)`, `J J' = (N_J)`, `p ∤ N_I N_J`);
so `I` and `J` have the same ideal class. -/
theorem span_mul_eq_of_isoFq [IsDomain R] (s : OAct R W L) {I I' J J' : Ideal R} {NI NJ : ℕ}
    (hI : I * I' = Ideal.span {(NI : R)}) (hNI : (NI : F) ≠ 0)
    (hJ : J * J' = Ideal.span {(NJ : R)}) (hNJ : (NJ : F) ≠ 0)
    (hq₁ : IsQuot (kerI s I) φ ψ n) (hq₂ : IsQuot (kerI s J) φ₂ ψ₂ n₂) (hiso : IsoFq W₁ W₂ L) :
    ∃ c : R, c ≠ 0 ∧ Ideal.span {c} * J = Ideal.span {(n₂ : R)} * I := by
  obtain ⟨u, v, hu, hv, hvu, huv, huf⟩ := hiso
  obtain ⟨c, hcP, hc⟩ := exists_mul_eq_of_isog s hI hNI hq₁ hq₂ hu huf
  obtain ⟨c', hc'P, hc'⟩ := exists_mul_eq_of_isog s hJ hNJ hq₂ hq₁ hv (frob_inv hvu huv huf)
  have hcc' : c * c' = (n : R) * n₂ := s.inj (AddMonoidHom.ext fun P => by
    rw [map_mul, map_mul]
    show s.ι c (s.ι c' P) = s.ι (n : R) (s.ι (n₂ : R) P)
    rw [hc'P, hcP, hq₁.dual2, map_nsmul, huv, map_nsmul, hq₂.dual1, s.natCast_apply, s.natCast_apply])
  have hn0 : (n : R) ≠ 0 := s.natCast_ne_zero hq₁.hn
  have hc0 : c ≠ 0 := fun h0 => by
    have h1 : (n : R) * n₂ ≠ 0 := mul_ne_zero hn0 (s.natCast_ne_zero hq₂.hn)
    rw [← hcc', h0, zero_mul] at h1
    exact h1 rfl
  refine ⟨c, hc0, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_singleton_mul_le_iff]
    intro j hj
    obtain ⟨i, hi, e⟩ := hc j hj
    rw [mul_comm c j, e]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hi
  · rw [Ideal.span_singleton_mul_le_iff]
    intro i hi
    obtain ⟨j, hj, e⟩ := hc' i hi
    have h2 : (n₂ : R) * i = c * j := by
      apply mul_left_cancel₀ hn0
      calc (n : R) * (n₂ * i) = (c * c') * i := by rw [hcc']; ring
        _ = c * (i * c') := by ring
        _ = (n : R) * (c * j) := by rw [e]; ring
    rw [h2]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hj

/-- **(b8), principal case**: `E/E[I] ≅ E` ⇒ `I` is principal. -/
theorem principal_of_isoFq [IsDomain R] (s : OAct R W L) {I I' : Ideal R} {NI : ℕ}
    (hI : I * I' = Ideal.span {(NI : R)}) (hNI : (NI : F) ≠ 0) (hq : IsQuot (kerI s I) φ ψ n)
    (hiso : IsoFq W₁ W L) : ∃ a : R, I = Ideal.span {a} := by
  have hq₀ : IsQuot (kerI s ⊤) (AddMonoidHom.id (Pt W L)) (AddMonoidHom.id _) 1 :=
    (kerI_top s).symm ▸ isQuot_bot
  have h1 : (⊤ : Ideal R) * ⊤ = Ideal.span {((1 : ℕ) : R)} := by
    rw [Nat.cast_one, Ideal.span_singleton_one, Ideal.top_mul]
  obtain ⟨c, -, hc⟩ := span_mul_eq_of_isoFq s hI hNI h1 (by rw [Nat.cast_one]; exact one_ne_zero) hq hq₀ hiso
  refine ⟨c, ?_⟩
  rw [Ideal.mul_top, Nat.cast_one, Ideal.span_singleton_one, Ideal.top_mul] at hc
  exact hc.symm

lemma natCast_mem_of_mul_eq {I J : Ideal R} {N : ℕ} (hIJ : I * J = Ideal.span {(N : R)}) : (N : R) ∈ I :=
  Ideal.mul_le.mpr (fun x hx y _ => I.mul_mem_right y hx) (by rw [hIJ]; exact Ideal.mem_span_singleton_self _)

/-- The `R`-structure `ι_I` on `E/E[I]` (`I J = (N)`, `p ∤ N`). -/
noncomputable def quotOAct [IsDomain R] {s : OAct R W L} {I J : Ideal R} {N : ℕ}
    (hq : IsQuot (kerI s I) φ ψ n) (hIJ : I * J = Ideal.span {(N : R)}) (hNF : (N : F) ≠ 0) : OAct R W₁ L :=
  ⟨ιq hq, ιq_injective hq (natCast_mem_of_mul_eq hIJ) hNF, ιq_mem hq,
    fun _ h => exists_ιq_eq hq hIJ hNF h⟩

lemma quotOAct_ι [IsDomain R] {s : OAct R W L} {I J : Ideal R} {N : ℕ}
    (hq : IsQuot (kerI s I) φ ψ n) (hIJ : I * J = Ideal.span {(N : R)}) (hNF : (N : F) ≠ 0) (α : R)
    (P : Pt W L) : (quotOAct hq hIJ hNF).ι α (φ P) = φ (s.ι α P) := ιq_spec hq α P

end Iso

end RPLib.DWS


