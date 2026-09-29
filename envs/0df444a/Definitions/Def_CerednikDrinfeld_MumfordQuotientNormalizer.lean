-- Prove2me | Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
-- name    : CerednikDrinfeld_MumfordQuotientNormalizer
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/cc273459-7cf6-5592-9380-04ac514ce5a8
-- title:
--   Conjugation transport and normaliser action on invariant fields
-- statement:
--   The standing context is a field $K$, a group $G$, and a commutative $K$-algebra $M$ which is a domain, with $G$ acting on $M$ by ring automorphisms that fix the image of $K$ (an action commuting with the $K$-scalars). The $G$-action extends to $\operatorname{Frac}(M)$, and for a subgroup $\Delta\le G$ the subfield $\mathcal K_\Delta=$ `invariantFieldOf K G M Δ` consists of those $x\in\operatorname{Frac}(M)$ with $\delta\cdot x=x$ for all $\delta\in\Delta$. Two transport lemmas record that if every $d\in\Delta'$ satisfies $g^{-1}dg\in\Delta$, then $g\cdot x\in\mathcal K_{\Delta'}$ for $x\in\mathcal K_\Delta$; in particular this holds with $\Delta'=\Delta$ when $g$ normalises $\Delta$. Given $g\in G$ and subgroups $\Delta,\Delta'$ together with the hypothesis $d\in\Delta'\iff g^{-1}dg\in\Delta$ (the conjugate subgroup is passed as a separate subgroup with its membership law rather than as a fixed term), `conjTransportRingEquiv` is the ring isomorphism $\mathcal K_\Delta\xrightarrow{\sim}\mathcal K_{\Delta'}$, $x\mapsto g\cdot x$, with inverse $y\mapsto g^{-1}\cdot y$, and `conjTransport` upgrades it to a $K$-algebra isomorphism; coercion lemmas identify the underlying elements of the map and its inverse. Two membership lemmas relate the hypothesis to standard spellings: $d$ lies in the image of $\Delta$ under conjugation by $g$ iff $g^{-1}dg\in\Delta$, and for $g$ in the normaliser of the underlying set of $\Delta$ one has $d\in\Delta\iff g^{-1}dg\in\Delta$. From this, `normalizerAct` is the group homomorphism from the normaliser of $\Delta$ to $\operatorname{Aut}_K(\mathcal K_\Delta)$ sending $n$ to $x\mapsto n\cdot x$. Further lemmas record that elements of $\Delta$ act as the identity (so the action factors through $N_G(\Delta)/\Delta$, the quotient itself not being formed), that for a normal subgroup this action agrees with `residualAct`, that it commutes with the semilinear coefficient action `AmbientSemilinearAut.coeffActOf`, and that transports for $\Delta_2\le\Delta_1$ agree along the resulting inclusion of invariant fields.
--
--   **Relation to Mathlib.** Built on Mathlib's `Subgroup.normalizer`, `MulAut.conj` and fixed-point subfields; the invariant field of a subgroup acting on $\operatorname{Frac}(M)$, its transport under conjugation, and the normaliser action on it are the project's own constructions.
--
--   **Where it is used.** These constructions belong to the Čerednik–Drinfeld / Mumford-curve layer, where function fields of quotients are presented as invariant subfields $\operatorname{Frac}(M)^\Delta$ of a fraction field carrying a group action; the normaliser action supplies the extra automorphisms (such as type-exchanging and Atkin–Lehner-style involutions) of such a quotient, and the compatibility with the semilinear coefficient action governs its behaviour under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_MumfordQuotientNormalizer.lean

import Definitions.Def_CerednikDrinfeld_MumfordQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CerednikDrinfeld.Mumford

namespace CerednikDrinfeld.Mumford

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]

theorem smul_mem_invariantFieldOf_of_forall_mem [IsDomain M] (g : G) {Δ Δ' : Subgroup G}
    (h : ∀ d : G, d ∈ Δ' → g⁻¹ * d * g ∈ Δ) {x : FractionRing M} (hx : x ∈ invariantFieldOf K G M Δ) :
    g • x ∈ invariantFieldOf K G M Δ' := fun d hd => by
  rw [← mul_smul, show d * g = g * (g⁻¹ * d * g) from by group, mul_smul]
  congr 1
  exact hx (g⁻¹ * d * g) (h d hd)

theorem smul_mem_invariantFieldOf_of_mem_normalizer [IsDomain M] (Δ : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (Δ : Set G))
    {x : FractionRing M} (hx : x ∈ invariantFieldOf K G M Δ) : g • x ∈ invariantFieldOf K G M Δ :=
  smul_mem_invariantFieldOf_of_forall_mem K G M g (fun d hd => (Subgroup.mem_normalizer_iff''.1 hg d).1 hd) hx

def conjTransportRingEquiv [IsDomain M] (g : G) (Δ Δ' : Subgroup G) (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) :
    ↥(invariantFieldOf K G M Δ) ≃+* ↥(invariantFieldOf K G M Δ') where
  toFun x := ⟨g • (x : FractionRing M),
    smul_mem_invariantFieldOf_of_forall_mem K G M g (fun d hd => (h d).1 hd) x.2⟩
  invFun y := ⟨g⁻¹ • (y : FractionRing M),
    smul_mem_invariantFieldOf_of_forall_mem K G M g⁻¹ (fun d hd => (h (g⁻¹⁻¹ * d * g⁻¹)).2 (by
      simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hd)) y.2⟩
  left_inv x := Subtype.ext (inv_smul_smul g (x : FractionRing M))
  right_inv y := Subtype.ext (smul_inv_smul g (y : FractionRing M))
  map_mul' x y := Subtype.ext (smul_mul' g (x : FractionRing M) y)
  map_add' x y := Subtype.ext (smul_add g (x : FractionRing M) y)

theorem coe_conjTransportRingEquiv [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) (x : ↥(invariantFieldOf K G M Δ)) :
    ((conjTransportRingEquiv K G M g Δ Δ' h x : ↥(invariantFieldOf K G M Δ')) : FractionRing M) =
      g • (x : FractionRing M) := rfl

def conjTransport [IsDomain M] (g : G) (Δ Δ' : Subgroup G) (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) :
    ↥(invariantFieldOf K G M Δ) ≃ₐ[K] ↥(invariantFieldOf K G M Δ') :=
  AlgEquiv.ofRingEquiv (f := conjTransportRingEquiv K G M g Δ Δ' h) (fun c => Subtype.ext (by
    rw [coe_conjTransportRingEquiv, algebraMap_invariantFieldOf_coe, algebraMap_invariantFieldOf_coe]
    exact smul_algebraMap_const K G M g c))

theorem coe_conjTransport [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) (x : ↥(invariantFieldOf K G M Δ)) :
    ((conjTransport K G M g Δ Δ' h x : ↥(invariantFieldOf K G M Δ')) : FractionRing M) = g • (x : FractionRing M) :=
  rfl

theorem coe_conjTransport_symm [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) (y : ↥(invariantFieldOf K G M Δ')) :
    (((conjTransport K G M g Δ Δ' h).symm y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) =
      g⁻¹ • (y : FractionRing M) :=
  rfl

theorem mem_map_conj_iff (g : G) (Δ : Subgroup G) (d : G) :
    d ∈ Δ.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * d * g ∈ Δ := by
  constructor
  · rintro ⟨e, he, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using he
  · intro hd
    exact ⟨g⁻¹ * d * g, hd, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_iff_of_mem_normalizer (Δ : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (Δ : Set G)) (d : G) :
    d ∈ Δ ↔ g⁻¹ * d * g ∈ Δ :=
  Subgroup.mem_normalizer_iff''.1 hg d

def normalizerAct [IsDomain M] (Δ : Subgroup G) :
    ↥(Subgroup.normalizer (Δ : Set G)) →* (↥(invariantFieldOf K G M Δ) ≃ₐ[K] ↥(invariantFieldOf K G M Δ)) where
  toFun n := conjTransport K G M (n : G) Δ Δ (mem_iff_of_mem_normalizer G Δ n.2)
  map_one' := AlgEquiv.ext fun x => Subtype.ext (one_smul G (x : FractionRing M))
  map_mul' n n' := AlgEquiv.ext fun x => Subtype.ext (mul_smul (n : G) (n' : G) (x : FractionRing M))

theorem coe_normalizerAct [IsDomain M] (Δ : Subgroup G) (n : ↥(Subgroup.normalizer (Δ : Set G))) (x : ↥(invariantFieldOf K G M Δ)) :
    ((normalizerAct K G M Δ n x : ↥(invariantFieldOf K G M Δ)) : FractionRing M) = (n : G) • (x : FractionRing M) :=
  rfl

theorem normalizerAct_eq_one_of_mem [IsDomain M] (Δ : Subgroup G) {n : ↥(Subgroup.normalizer (Δ : Set G))} (hn : (n : G) ∈ Δ) :
    normalizerAct K G M Δ n = 1 :=
  AlgEquiv.ext fun x => Subtype.ext (x.2 (n : G) hn)

theorem normalizerAct_eq_residualAct [IsDomain M] (N : Subgroup G) [N.Normal] (n : ↥(Subgroup.normalizer (N : Set G))) :
    normalizerAct K G M N n = residualAct K G M N (n : G) :=
  AlgEquiv.ext fun _ => Subtype.ext rfl

theorem coeffActOf_comm_conjTransport [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) (x : ↥(invariantFieldOf K G M Δ)) :
    AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ' s) (conjTransport K G M g Δ Δ' h x) =
      conjTransport K G M g Δ Δ' h (AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ s) x) :=
  Subtype.ext (by
    rw [AmbientSemilinearAut.coe_coeffActOf_toRingAut, coe_conjTransport, coe_conjTransport,
      AmbientSemilinearAut.coe_coeffActOf_toRingAut, AmbientSemilinearAut.fracMap_smul])

theorem coeffActOf_comm_normalizerAct [IsDomain M] (s : AmbientSemilinearAut K G M) (Δ : Subgroup G)
    (n : ↥(Subgroup.normalizer (Δ : Set G))) (x : ↥(invariantFieldOf K G M Δ)) :
    AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ s) (normalizerAct K G M Δ n x) =
      normalizerAct K G M Δ n (AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ s) x) :=
  coeffActOf_comm_conjTransport K G M s (n : G) Δ Δ (mem_iff_of_mem_normalizer G Δ n.2) x

theorem coe_conjTransport_eq_of_le [IsDomain M] (g : G) {Δ₁ Δ₂ Δ₁' Δ₂' : Subgroup G} (h12 : Δ₂ ≤ Δ₁)
    (h₁ : ∀ d : G, d ∈ Δ₁' ↔ g⁻¹ * d * g ∈ Δ₁) (h₂ : ∀ d : G, d ∈ Δ₂' ↔ g⁻¹ * d * g ∈ Δ₂)
    (x : ↥(invariantFieldOf K G M Δ₁)) :
    ((conjTransport K G M g Δ₂ Δ₂' h₂ ⟨x, invariantFieldOf_mono_of_le K G M h12 x.2⟩ : ↥(invariantFieldOf K G M Δ₂')) :
        FractionRing M) =
      ((conjTransport K G M g Δ₁ Δ₁' h₁ x : ↥(invariantFieldOf K G M Δ₁')) : FractionRing M) :=
  rfl

end CerednikDrinfeld.Mumford

end


