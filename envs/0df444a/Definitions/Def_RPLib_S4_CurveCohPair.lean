-- Prove2me | Definitions.Def_RPLib_S4_CurveCohPair
-- name    : RPLib_S4_CurveCohPair
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:01:56.87571+00:00
-- url     : https://prove2.me/theorems/87014e7d-5f2e-4441-8746-b7d112072085
-- title:
--   Cohomology of a profinite group relative to a family of inertia subgroups
-- statement:
--   Let $G$ be a topological group, $\Gamma \trianglelefteq G$ a normal subgroup, $\rho$ a representation of $G$ on a module $M$ over a commutative ring $k$ (with $M$ discrete), and $(I_s)_{s \in S}$ a family of subgroups of $G$ (the model is $G = \pi_1(U)$, $\Gamma = \pi_1(U \otimes \overline{\mathbb{F}}_q)$ and $I_s$ the inertia groups at the points at infinity). The file defines $H^0 = M^\Gamma$, $H^1$ as locally constant $1$-cocycles on $\Gamma$ modulo coboundaries, the compactly supported $H^1_c$ as $H^1$ of the mapping cone of $C^\bullet(\Gamma, M) \to \bigoplus_s C^\bullet(I_s \cap \Gamma, M)$, $H^2_c = M_\Gamma$, and the parabolic part $H^1_{par} = \ker(H^1 \to \bigoplus_s H^1(I_s \cap \Gamma))$, and proves the exact sequence $$0 \to H^0 \to \bigoplus_s M^{I_s} \to H^1_c \to H^1_{par} \to 0.$$ It also defines the operators $(T_\psi c)(g) = \rho(\psi)\, c(\psi^{-1} g \psi)$ for $\psi \in G$ (the geometric Frobenius is $T_{\varphi^{-1}}$) and shows that they commute with all maps of the sequence.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Galois Cohomology, Springer (1997), Chapter I, Section 2; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5 and Chapter V, Section 2

import Mathlib

/-!
# S4-CurveCoh, part 1: cohomology of a pair `(Γ, {I_s})` in the `π₁` model (generic algebra)

Setting (S4_DESIGN section 3, reviews R2/R5/R19):
* a topological group `G` (later `π₁(U)`), a normal subgroup `Γ` (later `π₁(U ⊗ F̄)`, the geometric fundamental
  group), a representation `ρ` of `G` on `M` over ANY commutative ring `k` (review END-2, decision R19), and a family
  `I : S → Subgroup G` (later the inertia groups at the geometric boundary points `s ∈ X̄ \ Ū`, review R5).

Definitions:
* `H0 = M^Γ`;
* `H1` = LOCALLY CONSTANT (continuous, `M` discrete) 1-cocycles on `Γ` modulo coboundaries; part 2 shows it is the
  colimit of the finite-level `H¹` over open normal subgroups (covers);
* `H1c` = `H¹` of the mapping cone of `C^*(Γ, M) → ⊕_s C^*(I_s ∩ Γ, M)`: pairs `(c, b)` of a cocycle `c` and boundary
  trivialisations `b_s` with `c g = g • b_s - b_s` on `I_s ∩ Γ`, modulo `(d m, (m)_s)`;
* `H2c` = the coinvariants `M_Γ` (definition kept by review R2; the Tate twist `(-1)` enters the Frobenius as a scalar);
* the exact sequence `0 → H⁰ → ⊕_s M^{I_s} → H¹_c → H¹_par → 0`, `H¹_par = ker (H¹ → ⊕_s H¹(I_s ∩ Γ))`;
* the operators `T_ψ` (`ψ ∈ G`): `(T_ψ c)(g) = ρ(ψ) c(ψ⁻¹ g ψ)`. The GEOMETRIC Frobenius is `F = T_{φ⁻¹}` for an
  arithmetic Frobenius lift `φ`; on `H2c` it is `q • ρ(φ⁻¹)` (geometric Frobenius acts on `ℤ/lⁿ(-1)` by `q`).
  All operators commute with the maps of the exact sequence.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G)

/-! ## Degree 0 and degree 1 -/

/-- `H⁰ := M^Γ`, the invariants of the geometric group. -/
def H0 : Submodule k M := Representation.invariants (ρ.comp Γ.subtype)

theorem mem_H0 (m : M) : m ∈ H0 ρ Γ ↔ ∀ g : Γ, ρ g m = m := Iff.rfl

/-- Locally constant (= continuous for discrete `M`) inhomogeneous 1-cocycles `Γ → M`. -/
def Z1 : Submodule k (Γ → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + ρ g (c h)}
  add_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨hc.add hd, fun g h => ?_⟩
    simp only [Pi.add_apply, hc', hd', map_add]
    abel
  zero_mem' := ⟨IsLocallyConstant.zero, fun g h => by simp⟩
  smul_mem' := by
    rintro a c ⟨hc, hc'⟩
    refine ⟨hc.comp (a • ·), fun g h => ?_⟩
    simp only [Pi.smul_apply, hc', smul_add, map_smul]

theorem mem_Z1 (c : Γ → M) :
    c ∈ Z1 ρ Γ ↔ IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + ρ g (c h) := Iff.rfl

/-- 1-coboundaries `g ↦ g • m - m` that are locally constant. -/
def B1 : Submodule k (Γ → M) where
  carrier := {c | c ∈ Z1 ρ Γ ∧ ∃ m : M, ∀ g : Γ, c g = ρ g m - m}
  add_mem' := by
    rintro c d ⟨hc, m, hm⟩ ⟨hd, n, hn⟩
    refine ⟨(Z1 ρ Γ).add_mem hc hd, m + n, fun g => ?_⟩
    simp only [Pi.add_apply, hm, hn, map_add]
    abel
  zero_mem' := ⟨(Z1 ρ Γ).zero_mem, 0, fun g => by simp⟩
  smul_mem' := by
    rintro a c ⟨hc, m, hm⟩
    exact ⟨(Z1 ρ Γ).smul_mem a hc, a • m, fun g => by simp [hm, smul_sub]⟩

theorem mem_B1 (c : Γ → M) : c ∈ B1 ρ Γ ↔ c ∈ Z1 ρ Γ ∧ ∃ m : M, ∀ g : Γ, c g = ρ g m - m := Iff.rfl

theorem B1_le_Z1 : B1 ρ Γ ≤ Z1 ρ Γ := fun _ h => h.1

/-- `H¹(Γ, M)` with continuous (locally constant) cochains. -/
abbrev H1 : Type := ↥(Z1 ρ Γ) ⧸ (B1 ρ Γ).comap (Z1 ρ Γ).subtype

/-- The class of a cocycle. -/
noncomputable def H1.mk : Z1 ρ Γ →ₗ[k] H1 ρ Γ := Submodule.mkQ _

theorem Z1_one {c : Γ → M} (hc : c ∈ Z1 ρ Γ) : c 1 = 0 := by
  have h := hc.2 1 1
  simpa using h

theorem Z1_inv {c : Γ → M} (hc : c ∈ Z1 ρ Γ) (g : Γ) : c g⁻¹ = -ρ (g⁻¹ : Γ) (c g) := by
  have h := hc.2 g g⁻¹
  rw [mul_inv_cancel, Z1_one ρ Γ hc] at h
  have h2 : ρ (g : G) (c g⁻¹) = -c g := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h.symm
  have h3 := congrArg (ρ ((g : G)⁻¹)) h2
  rw [Representation.inv_self_apply, map_neg] at h3
  simpa using h3

/-- A cocycle that is a coboundary on `g` is a coboundary on the conjugate `η g η⁻¹`, with the conjugated
trivialisation `ρ η b - c η`. -/
theorem Z1_conj {c : Γ → M} (hc : c ∈ Z1 ρ Γ) (η g : Γ) (b : M) (hg : c g = ρ g b - b) :
    c (η * g * η⁻¹) = ρ (η * g * η⁻¹ : Γ) (ρ η b - c η) - (ρ η b - c η) := by
  rw [hc.2 (η * g) η⁻¹, hc.2 η g, hg, Z1_inv ρ Γ hc η]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply, map_sub, map_neg,
    Representation.inv_self_apply]
  abel

/-! ## The cone: compactly supported `H¹` -/

variable {S : Type} (I : S → Subgroup G)

/-- Relative 1-cocycles of the pair `(Γ, {I_s})`: degree-1 cocycles of the mapping cone of
`C^*(Γ, M) → ⊕_s C^*(I_s ∩ Γ, M)`, i.e. a cocycle `c` with boundary trivialisations `b_s`. -/
def Z1c : Submodule k ((Γ → M) × (S → M)) where
  carrier := {p | p.1 ∈ Z1 ρ Γ ∧ ∀ (s : S) (g : Γ), (g : G) ∈ I s → p.1 g = ρ g (p.2 s) - p.2 s}
  add_mem' := by
    rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
    refine ⟨(Z1 ρ Γ).add_mem hp hq, fun s g hg => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, hp' s g hg, hq' s g hg, map_add]
    abel
  zero_mem' := ⟨(Z1 ρ Γ).zero_mem, fun s g _ => by simp⟩
  smul_mem' := by
    rintro a p ⟨hp, hp'⟩
    refine ⟨(Z1 ρ Γ).smul_mem a hp, fun s g hg => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, hp' s g hg, map_smul, smul_sub]

theorem mem_Z1c (p : (Γ → M) × (S → M)) : p ∈ Z1c ρ Γ I ↔
    p.1 ∈ Z1 ρ Γ ∧ ∀ (s : S) (g : Γ), (g : G) ∈ I s → p.1 g = ρ g (p.2 s) - p.2 s := Iff.rfl

/-- Relative coboundaries `(d m, (m)_s)`. -/
def B1c : Submodule k ((Γ → M) × (S → M)) where
  carrier := {p | p ∈ Z1c ρ Γ I ∧ ∃ m : M, (∀ g : Γ, p.1 g = ρ g m - m) ∧ ∀ s, p.2 s = m}
  add_mem' := by
    rintro p q ⟨hp, m, hm, hm'⟩ ⟨hq, n, hn, hn'⟩
    refine ⟨(Z1c ρ Γ I).add_mem hp hq, m + n, fun g => ?_, fun s => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, hm, hn, map_add]
      abel
    · simp [hm', hn']
  zero_mem' := ⟨(Z1c ρ Γ I).zero_mem, 0, fun g => by simp, fun s => by simp⟩
  smul_mem' := by
    rintro a p ⟨hp, m, hm, hm'⟩
    exact ⟨(Z1c ρ Γ I).smul_mem a hp, a • m, fun g => by simp [hm, smul_sub], fun s => by simp [hm']⟩

theorem mem_B1c (p : (Γ → M) × (S → M)) : p ∈ B1c ρ Γ I ↔
    p ∈ Z1c ρ Γ I ∧ ∃ m : M, (∀ g : Γ, p.1 g = ρ g m - m) ∧ ∀ s, p.2 s = m := Iff.rfl

/-- `H¹_c(Ū, M)`: `H¹` of the mapping cone (relative cohomology of `(Γ, {I_s})`). -/
abbrev H1c : Type := ↥(Z1c ρ Γ I) ⧸ (B1c ρ Γ I).comap (Z1c ρ Γ I).subtype

/-- The class of a relative cocycle. -/
noncomputable def H1c.mk : Z1c ρ Γ I →ₗ[k] H1c ρ Γ I := Submodule.mkQ _

/-- `⊕_s M^{I_s}` (only `I_s ∩ Γ` matters). -/
def bdryInv : Submodule k (S → M) where
  carrier := {b | ∀ (s : S) (g : Γ), (g : G) ∈ I s → ρ g (b s) = b s}
  add_mem' := by
    intro b b' hb hb' s g hg
    simp [hb s g hg, hb' s g hg]
  zero_mem' := fun s g _ => by simp
  smul_mem' := by
    intro a b hb s g hg
    simp [hb s g hg]

theorem mem_bdryInv (b : S → M) :
    b ∈ bdryInv ρ Γ I ↔ ∀ (s : S) (g : Γ), (g : G) ∈ I s → ρ g (b s) = b s := Iff.rfl

/-- Cocycles that are coboundaries on every `I_s ∩ Γ` (unramified at the boundary). -/
def Z1par : Submodule k (Γ → M) where
  carrier := {c | c ∈ Z1 ρ Γ ∧ ∀ s : S, ∃ b : M, ∀ g : Γ, (g : G) ∈ I s → c g = ρ g b - b}
  add_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨(Z1 ρ Γ).add_mem hc hd, fun s => ?_⟩
    obtain ⟨b, hb⟩ := hc' s
    obtain ⟨b', hb'⟩ := hd' s
    refine ⟨b + b', fun g hg => ?_⟩
    simp only [Pi.add_apply, hb g hg, hb' g hg, map_add]
    abel
  zero_mem' := ⟨(Z1 ρ Γ).zero_mem, fun s => ⟨0, fun g _ => by simp⟩⟩
  smul_mem' := by
    rintro a c ⟨hc, hc'⟩
    refine ⟨(Z1 ρ Γ).smul_mem a hc, fun s => ?_⟩
    obtain ⟨b, hb⟩ := hc' s
    exact ⟨a • b, fun g hg => by simp [hb g hg, smul_sub]⟩

/-- `H¹_par = ker (H¹(Γ, M) → ⊕_s H¹(I_s ∩ Γ, M))`, as the image of `Z1par`. -/
noncomputable def H1par : Submodule k (H1 ρ Γ) :=
  ((Z1par ρ Γ I).comap (Z1 ρ Γ).subtype).map (H1.mk ρ Γ)

/-! ## The maps of the exact sequence `0 → H⁰ → ⊕_s M^{I_s} → H¹_c → H¹_par → 0` -/

/-- `H⁰ → ⊕_s M^{I_s}`, the diagonal. -/
def h0ToBdry : H0 ρ Γ →ₗ[k] bdryInv ρ Γ I where
  toFun m := ⟨fun _ => m, fun _ g _ => (mem_H0 ρ Γ _).1 m.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem zero_bdry_mem (b : bdryInv ρ Γ I) : ((0 : Γ → M), (b : S → M)) ∈ Z1c ρ Γ I :=
  ⟨(Z1 ρ Γ).zero_mem, fun s g hg => by simp [(mem_bdryInv ρ Γ I _).1 b.2 s g hg]⟩

/-- `⊕_s M^{I_s} → H¹_c`, `b ↦ [(0, b)]`. -/
noncomputable def bdryToH1c : bdryInv ρ Γ I →ₗ[k] H1c ρ Γ I :=
  H1c.mk ρ Γ I ∘ₗ LinearMap.codRestrict (Z1c ρ Γ I)
    (LinearMap.inr k (Γ → M) (S → M) ∘ₗ (bdryInv ρ Γ I).subtype) (fun b => zero_bdry_mem ρ Γ I b)

/-- Forget the boundary data. -/
def z1cToZ1 : Z1c ρ Γ I →ₗ[k] Z1 ρ Γ where
  toFun p := ⟨p.1.1, p.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `H¹_c → H¹`. -/
noncomputable def h1cToH1 : H1c ρ Γ I →ₗ[k] H1 ρ Γ :=
  Submodule.mapQ _ _ (z1cToZ1 ρ Γ I) (by
    rintro p ⟨_, m, hm, _⟩
    exact ⟨p.2.1, m, hm⟩)

theorem h1cToH1_mk (p : Z1c ρ Γ I) : h1cToH1 ρ Γ I (H1c.mk ρ Γ I p) = H1.mk ρ Γ (z1cToZ1 ρ Γ I p) := rfl

theorem bdryToH1c_apply (b : bdryInv ρ Γ I) :
    bdryToH1c ρ Γ I b = H1c.mk ρ Γ I ⟨(0, b), zero_bdry_mem ρ Γ I b⟩ := rfl

theorem h0ToBdry_injective [Nonempty S] : Function.Injective (h0ToBdry ρ Γ I) := by
  intro m m' h
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  exact Subtype.ext (congrFun (congrArg Subtype.val h) s)

/-- Exactness at `⊕_s M^{I_s}`. -/
theorem exact_h0ToBdry_bdryToH1c : Function.Exact (h0ToBdry ρ Γ I) (bdryToH1c ρ Γ I) := by
  intro b
  rw [bdryToH1c_apply, H1c.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  constructor
  · rintro ⟨_, m, hm, hm'⟩
    have hm0 : m ∈ H0 ρ Γ := fun g => by
      have h0 : (0 : M) = ρ g m - m := hm g
      exact (sub_eq_zero.mp h0.symm)
    exact ⟨⟨m, hm0⟩, Subtype.ext (funext fun s => (hm' s).symm)⟩
  · rintro ⟨m, rfl⟩
    refine ⟨zero_bdry_mem ρ Γ I _, m, fun g => ?_, fun s => rfl⟩
    simp [(mem_H0 ρ Γ _).1 m.2 g]

/-- Exactness at `H¹_c`. -/
theorem exact_bdryToH1c_h1cToH1 : Function.Exact (bdryToH1c ρ Γ I) (h1cToH1 ρ Γ I) := by
  intro x
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
    change h1cToH1 ρ Γ I (H1c.mk ρ Γ I p) = 0 at hx
    rw [h1cToH1_mk, H1.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx
    obtain ⟨_, m, hm⟩ := hx
    have hm' : ∀ g : Γ, (p : (Γ → M) × (S → M)).1 g = ρ g m - m := hm
    have hmem : (fun s => (p : (Γ → M) × (S → M)).2 s - m) ∈ bdryInv ρ Γ I := by
      intro s g hg
      have h1 := p.2.2 s g hg
      rw [hm' g] at h1
      show ρ g ((p : (Γ → M) × (S → M)).2 s - m) = (p : (Γ → M) × (S → M)).2 s - m
      rw [map_sub, sub_eq_sub_iff_sub_eq_sub]
      exact h1.symm
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [bdryToH1c_apply]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    refine ⟨(Z1c ρ Γ I).sub_mem (zero_bdry_mem ρ Γ I _) p.2, -m, fun g => ?_, fun s => ?_⟩
    · show (0 : Γ → M) g - (p : (Γ → M) × (S → M)).1 g = ρ g (-m) - -m
      rw [hm' g, map_neg]
      simp only [Pi.zero_apply]
      abel
    · show ((p : (Γ → M) × (S → M)).2 s - m) - (p : (Γ → M) × (S → M)).2 s = -m
      abel
  · rintro ⟨b, rfl⟩
    rw [bdryToH1c_apply, h1cToH1_mk, H1.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    exact ⟨(Z1 ρ Γ).zero_mem, 0, fun g => by simp [z1cToZ1]⟩

/-- Exactness at the right end: the image of `H¹_c → H¹` is `H¹_par`. -/
theorem range_h1cToH1 : LinearMap.range (h1cToH1 ρ Γ I) = H1par ρ Γ I := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ y
    refine ⟨z1cToZ1 ρ Γ I p, ⟨p.2.1, fun s => ⟨p.1.2 s, fun g hg => p.2.2 s g hg⟩⟩, rfl⟩
  · rintro ⟨c, ⟨hcZ, hc⟩, rfl⟩
    choose b hb using hc
    refine ⟨H1c.mk ρ Γ I ⟨((c : Γ → M), b), hcZ, fun s g hg => hb s g hg⟩, rfl⟩

/-! ## Frobenius operators -/

section Frob

variable [IsTopologicalGroup G] [hΓ : Γ.Normal]

/-- Conjugation `g ↦ ψ⁻¹ g ψ` on the normal subgroup `Γ`. -/
def conjΓ (ψ : G) (g : Γ) : Γ := ⟨ψ⁻¹ * g * ψ, by simpa using hΓ.conj_mem (g : G) g.2 ψ⁻¹⟩

@[simp] theorem conjΓ_val (ψ : G) (g : Γ) : (conjΓ Γ ψ g : G) = ψ⁻¹ * g * ψ := rfl

theorem conjΓ_mul (ψ : G) (g h : Γ) : conjΓ Γ ψ (g * h) = conjΓ Γ ψ g * conjΓ Γ ψ h := by
  ext
  simp [mul_assoc]

theorem continuous_conjΓ (ψ : G) : Continuous (conjΓ Γ ψ) := by
  have : Continuous fun g : Γ => ψ⁻¹ * (g : G) * ψ :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  exact this.subtype_mk _

theorem rho_conj (ψ : G) (g : Γ) (x : M) : ρ ψ (ρ (conjΓ Γ ψ g) x) = ρ g (ρ ψ x) := by
  have e : ψ * (ψ⁻¹ * (g : G) * ψ) = (g : G) * ψ := by group
  calc ρ ψ (ρ (conjΓ Γ ψ g) x) = ρ (ψ * (ψ⁻¹ * (g : G) * ψ)) x := by rw [map_mul]; rfl
    _ = ρ g (ρ ψ x) := by rw [e, map_mul]; rfl

theorem rho_conj' (ψ : G) (g : Γ) (x : M) : ρ (conjΓ Γ ψ⁻¹ g) (ρ ψ x) = ρ ψ (ρ g x) := by
  have e : ψ⁻¹⁻¹ * (g : G) * ψ⁻¹ * ψ = ψ * g := by group
  calc ρ (conjΓ Γ ψ⁻¹ g) (ρ ψ x) = ρ (ψ⁻¹⁻¹ * (g : G) * ψ⁻¹ * ψ) x := by rw [map_mul]; rfl
    _ = ρ ψ (ρ g x) := by rw [e, map_mul]; rfl

/-- Frobenius on `H⁰`: `m ↦ ρ(ψ) m`. -/
def frobH0 (ψ : G) : H0 ρ Γ →ₗ[k] H0 ρ Γ :=
  (ρ ψ).restrict (fun m hm => fun g => by
    show ρ g (ρ ψ m) = ρ ψ m
    rw [← rho_conj ρ Γ ψ g, (mem_H0 ρ Γ m).1 hm])

/-- The cochain operator `(T_ψ c)(g) = ρ(ψ) (c (ψ⁻¹ g ψ))`. -/
def twist (ψ : G) : (Γ → M) →ₗ[k] (Γ → M) where
  toFun c g := ρ ψ (c (conjΓ Γ ψ g))
  map_add' c d := by
    funext g
    simp
  map_smul' a c := by
    funext g
    simp

theorem twist_apply (ψ : G) (c : Γ → M) (g : Γ) : twist ρ Γ ψ c g = ρ ψ (c (conjΓ Γ ψ g)) := rfl

theorem twist_mem_Z1 (ψ : G) {c : Γ → M} (hc : c ∈ Z1 ρ Γ) : twist ρ Γ ψ c ∈ Z1 ρ Γ := by
  refine ⟨(hc.1.comp_continuous (continuous_conjΓ Γ ψ)).comp (ρ ψ), fun g h => ?_⟩
  rw [twist_apply, twist_apply, twist_apply, conjΓ_mul, hc.2, map_add, rho_conj]

theorem twist_mem_B1 (ψ : G) {c : Γ → M} (hc : c ∈ B1 ρ Γ) : twist ρ Γ ψ c ∈ B1 ρ Γ := by
  obtain ⟨hcZ, m, hm⟩ := hc
  refine ⟨twist_mem_Z1 ρ Γ ψ hcZ, ρ ψ m, fun g => ?_⟩
  rw [twist_apply, hm, map_sub, rho_conj]

/-- Frobenius on `H¹`. -/
noncomputable def frobH1 (ψ : G) : H1 ρ Γ →ₗ[k] H1 ρ Γ :=
  Submodule.mapQ _ _ ((twist ρ Γ ψ).restrict (fun c hc => twist_mem_Z1 ρ Γ ψ hc))
    (fun c hc => twist_mem_B1 ρ Γ ψ hc)

variable {S : Type} (I : S → Subgroup G)

/-- The cone operator: `(c, b) ↦ (T_ψ c, s ↦ ρ(ψ) (ρ(h_s) b_{τ s} - c(h_s)))`. -/
def twistc (ψ : G) (τ : S → S) (h : S → Γ) : ((Γ → M) × (S → M)) →ₗ[k] ((Γ → M) × (S → M)) where
  toFun p := (twist ρ Γ ψ p.1, fun s => ρ ψ (ρ (h s) (p.2 (τ s)) - p.1 (h s)))
  map_add' p q := by
    refine Prod.ext (map_add _ _ _) (funext fun s => ?_)
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, map_add, map_sub]
    abel
  map_smul' a p := by
    refine Prod.ext (map_smul _ _ _) (funext fun s => ?_)
    simp [smul_sub]

theorem twistc_fst (ψ : G) (τ : S → S) (h : S → Γ) (p : (Γ → M) × (S → M)) :
    (twistc ρ Γ ψ τ h p).1 = twist ρ Γ ψ p.1 := rfl

theorem twistc_snd (ψ : G) (τ : S → S) (h : S → Γ) (p : (Γ → M) × (S → M)) (s : S) :
    (twistc ρ Γ ψ τ h p).2 s = ρ ψ (ρ (h s) (p.2 (τ s)) - p.1 (h s)) := rfl

/-- The compatibility of a Frobenius lift with the boundary: `ψ⁻¹ (I_s ∩ Γ) ψ ⊆ h_s I_{τ s} h_s⁻¹`. -/
def BdryCompat (ψ : G) (τ : S → S) (h : S → Γ) : Prop :=
  ∀ (s : S) (g : Γ), (g : G) ∈ I s → (h s : G)⁻¹ * (ψ⁻¹ * g * ψ) * h s ∈ I (τ s)

theorem bdryCompat_mem {ψ : G} {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I ψ τ h) (s : S) (g : Γ)
    (hg : (g : G) ∈ I s) : (((h s)⁻¹ * conjΓ Γ ψ g * h s : Γ) : G) ∈ I (τ s) := by
  simpa [mul_assoc] using hI s g hg

theorem twistc_mem_Z1c (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h)
    {p : (Γ → M) × (S → M)} (hp : p ∈ Z1c ρ Γ I) : twistc ρ Γ ψ τ h p ∈ Z1c ρ Γ I := by
  refine ⟨twist_mem_Z1 ρ Γ ψ hp.1, fun s g hg => ?_⟩
  have hg' := hp.2 (τ s) _ (bdryCompat_mem Γ I hI s g hg)
  have hc := Z1_conj ρ Γ hp.1 (h s) _ _ hg'
  have he : h s * ((h s)⁻¹ * conjΓ Γ ψ g * h s) * (h s)⁻¹ = conjΓ Γ ψ g := by group
  rw [he] at hc
  rw [twistc_fst, twistc_snd, twist_apply, hc, map_sub, rho_conj]

theorem twistc_mem_B1c (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h)
    {p : (Γ → M) × (S → M)} (hp : p ∈ B1c ρ Γ I) : twistc ρ Γ ψ τ h p ∈ B1c ρ Γ I := by
  obtain ⟨hpZ, m, hm1, hm2⟩ := hp
  refine ⟨twistc_mem_Z1c ρ Γ I ψ τ h hI hpZ, ρ ψ m, fun g => ?_, fun s => ?_⟩
  · rw [twistc_fst, twist_apply, hm1, map_sub, rho_conj]
  · rw [twistc_snd, hm2, hm1]
    simp

/-- Frobenius on `H¹_c`. -/
noncomputable def frobH1c (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) :
    H1c ρ Γ I →ₗ[k] H1c ρ Γ I :=
  Submodule.mapQ _ _ ((twistc ρ Γ ψ τ h).restrict (fun p hp => twistc_mem_Z1c ρ Γ I ψ τ h hI hp))
    (fun p hp => twistc_mem_B1c ρ Γ I ψ τ h hI hp)

theorem frobBdry_mem (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h)
    {b : S → M} (hb : b ∈ bdryInv ρ Γ I) :
    (fun s => ρ ψ (ρ (h s) (b (τ s)))) ∈ bdryInv ρ Γ I := by
  intro s g hg
  have h1 := hb (τ s) _ (bdryCompat_mem Γ I hI s g hg)
  show ρ g (ρ ψ (ρ (h s) (b (τ s)))) = ρ ψ (ρ (h s) (b (τ s)))
  rw [← rho_conj ρ Γ ψ g]
  congr 1
  calc ρ (conjΓ Γ ψ g) (ρ (h s) (b (τ s)))
      = ρ (h s) (ρ (((h s)⁻¹ * conjΓ Γ ψ g * h s : Γ) : G) (b (τ s))) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply,
          Representation.self_inv_apply]
    _ = ρ (h s) (b (τ s)) := by rw [h1]

/-- Frobenius on `⊕_s M^{I_s}`: `b ↦ (s ↦ ρ(ψ) ρ(h_s) b_{τ s})`. -/
def frobBdry (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) :
    bdryInv ρ Γ I →ₗ[k] bdryInv ρ Γ I where
  toFun b := ⟨fun s => ρ ψ (ρ (h s) (b.1 (τ s))), frobBdry_mem ρ Γ I ψ τ h hI b.2⟩
  map_add' b b' := by
    ext s
    simp
  map_smul' a b := by
    ext s
    simp

/-- `H²_c := M_Γ`, the coinvariants (definition kept by review R2; S4-PD proves it is the cone's `H²`). -/
abbrev H2c : Type := Representation.Coinvariants (ρ.comp Γ.subtype)

/-- Frobenius on `H²_c`: `χ • ρ(ψ)` on coinvariants. For the geometric Frobenius `ψ = φ⁻¹` and `χ = q` this is `F`
on `M_Γ(-1)` (geometric Frobenius acts on `ℤ/lⁿ(-1)` by multiplication by `q`). -/
noncomputable def frobH2c (ψ : G) (χ : k) : H2c ρ Γ →ₗ[k] H2c ρ Γ :=
  Representation.Coinvariants.lift _ (χ • (Representation.Coinvariants.mk _ ∘ₗ ρ ψ)) (fun g =>
    LinearMap.ext fun x => by
      have h := Representation.Coinvariants.mk_self_apply (ρ.comp Γ.subtype) (conjΓ Γ ψ⁻¹ g) (ρ ψ x)
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at h
      rw [rho_conj'] at h
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, h])

theorem frobH2c_mk (ψ : G) (χ : k) (x : M) :
    frobH2c ρ Γ ψ χ (Representation.Coinvariants.mk _ x) = χ • Representation.Coinvariants.mk _ (ρ ψ x) := rfl

/-! ### Frobenius commutes with the exact sequence -/

theorem frobBdry_h0ToBdry (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) (m : H0 ρ Γ) :
    frobBdry ρ Γ I ψ τ h hI (h0ToBdry ρ Γ I m) = h0ToBdry ρ Γ I (frobH0 ρ Γ ψ m) := by
  ext s
  show ρ ψ (ρ (h s) m.1) = ρ ψ m.1
  rw [(mem_H0 ρ Γ _).1 m.2]

theorem frobH1c_bdryToH1c (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) (b : bdryInv ρ Γ I) :
    frobH1c ρ Γ I ψ τ h hI (bdryToH1c ρ Γ I b) = bdryToH1c ρ Γ I (frobBdry ρ Γ I ψ τ h hI b) := by
  rw [bdryToH1c_apply, bdryToH1c_apply]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  refine Prod.ext (funext fun g => ?_) (funext fun s => ?_)
  · show ρ ψ ((0 : Γ → M) (conjΓ Γ ψ g)) = 0
    simp
  · show ρ ψ (ρ (h s) (b.1 (τ s)) - (0 : Γ → M) (h s)) = ρ ψ (ρ (h s) (b.1 (τ s)))
    simp

theorem h1cToH1_frobH1c (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) (x : H1c ρ Γ I) :
    h1cToH1 ρ Γ I (frobH1c ρ Γ I ψ τ h hI x) = frobH1 ρ Γ ψ (h1cToH1 ρ Γ I x) := by
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

end Frob

/-! ## Sanity: constant coefficients -/

section Constant

variable (I : S → Subgroup G)

/-- `H⁰` of a representation on which `Γ` acts trivially is everything. -/
theorem H0_eq_top_of_trivial (h : ∀ g : Γ, ρ g = 1) : H0 ρ Γ = ⊤ :=
  eq_top_iff.2 fun m _ => fun g => by
    show ρ g m = m
    rw [h g]; rfl

/-- For constant coefficients every boundary vector is invariant. -/
theorem bdryInv_eq_top_of_trivial (h : ∀ g : Γ, ρ g = 1) : bdryInv ρ Γ I = ⊤ :=
  eq_top_iff.2 fun b _ => fun s g _ => by
    show ρ g (b s) = b s
    rw [h g]; rfl

end Constant

end

end CurveCoh
end RamanujanPetersson


