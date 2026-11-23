-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_GramSubmersionSplit
-- name    : Formalism_FlagUnipotentLattices_GramSubmersionSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:50.931415+00:00
-- url     : https://prove2.me/theorems/b09b6c16-f181-44b3-bbf0-e054ad9a2e64
-- title:
--   Gram Submersion Split
-- statement:
--   Definitions and structural lemmas for Gram Submersion Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/GramSubmersionSplit.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLatticeCounting.S4
open Finset
open Formalism.SL.IwahoriBlocks (IsHerm eich)
section defs
variable {E : Type*} [CommRing E] {V : Type*} [AddCommGroup V] [Module E V]
def InRR (O : Subring E) (th a a' : E) : Prop := a' ∈ O ∧ ∃ x ∈ O, a + a' = th * x
def latM (O : Subring E) (θ : Eˣ) {n : ℕ} (f f' : Fin n → V) : Submodule O V :=
  Submodule.span O (Set.range f ∪ Set.range (fun i => ((θ⁻¹ : Eˣ) : E) • (f' i - f i)))
def latMJ (O : Subring E) (θ : Eˣ) {n : ℕ} (f f' : Fin n → V) (J : ℕ) : Submodule O V :=
  Submodule.span O (f '' {i | i.val < J} ∪ (fun i => ((θ⁻¹ : Eˣ) : E) • (f' i - f i)) '' {i | i.val < J})
def spanY (E : Type*) [CommRing E] {V : Type*} [AddCommGroup V] [Module E V] {n : ℕ} (f f' : Fin n → V)
    (J : ℕ) : Submodule E V :=
  Submodule.span E (f '' {i | i.val < J} ∪ f' '' {i | i.val < J})
def LevelLe (O : Subring E) (abelian₂ : AddSubgroup V) (θ : Eˣ) {n : ℕ} (f f' : Fin n → V) (J : ℕ) : Prop :=
  ∀ a a' : Fin n → E, ((θ⁻¹ : Eˣ) : E) • ((∑ i, a i • f i) + (∑ i, a' i • f' i)) ∈ abelian₂ →
    ∀ i, J ≤ i.val → InRR O (θ : E) (a i) (a' i)
end defs
section defs2
variable {E V : Type*} [CommRing E] [StarRing E] [AddCommGroup V] [Module E V]
def capSub {h : V →ₗ[E] V →ₗ⋆[E] E} {O : Subring E} {abelian₂ : AddSubgroup V}
    {O' Lam' : Type*} [CommRing O'] [StarRing O'] [AddCommGroup Lam'] [Module O' Lam']
    {h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O'} {io : O' →+* E} {j : Lam' →+ V}
    (hm : LatModel h O abelian₂ h' io j) (Z : Submodule E V) : Submodule O' Lam' where
  carrier := {w | j w ∈ Z}
  add_mem' := by
    intro a b ha hb
    show j (a + b) ∈ Z
    rw [map_add]; exact Z.add_mem ha hb
  zero_mem' := by
    show j 0 ∈ Z
    rw [map_zero]; exact Z.zero_mem
  smul_mem' := by
    intro c x hx
    show j (c • x) ∈ Z
    rw [hm.j_smul]; exact Z.smul_mem _ hx
def dualIn (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (Z : Submodule E V) :
    AddSubgroup V where
  carrier := {v | v ∈ Z ∧ ∀ w ∈ abelian₂, w ∈ Z → h w v ∈ O}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Z.add_mem ha hb, fun w hw hz => ?_⟩
    rw [map_add]; exact O.add_mem (ha' w hw hz) (hb' w hw hz)
  zero_mem' := ⟨Z.zero_mem, fun w _ _ => by rw [map_zero]; exact O.zero_mem⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Z.neg_mem ha, fun w hw hz => ?_⟩
    rw [map_neg]; exact O.neg_mem (ha' w hw hz)
end defs2
def UnramTrace : Prop :=
  ∀ (o O : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
    [Algebra o O], Unram o O →
    (∀ y : O, star y = y → ∃ c : o, algebraMap o O c = y) ∧
    (∀ y : O, ∃ t : o, algebraMap o O t = y + star y) ∧
    (∀ y : O, star y = y → ∃ s : O, s + star s = y)
def TraceOntoV : Prop :=
  ∀ (o O' : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O'] [StarRing O']
    [Algebra o O'] (E : Type) [CommRing E] [StarRing E] (O : Subring E) (io : O' →+* E),
    Unram o O' → Function.Injective io → (∀ c, c ∈ O ↔ ∃ a, io a = c) →
    (∀ a, io (star a) = star (io a)) →
    ∀ c ∈ O, star c = c → ∃ s ∈ O, s + star s = c
def SameTraceSelfDual : Prop :=
  ∀ (o O' : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O'] [StarRing O']
    [Algebra o O']
    (La' Lb' : Type) [AddCommGroup La'] [Module O' La'] [Module.Free O' La'] [Module.Finite O' La']
    [AddCommGroup Lb'] [Module O' Lb'] [Module.Free O' Lb'] [Module.Finite O' Lb']
    (ha' : La' →ₗ[O'] La' →ₗ⋆[O'] O') (hb' : Lb' →ₗ[O'] Lb' →ₗ⋆[O'] O')
    (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (La Lb : AddSubgroup V) (io : O' →+* E)
    (ja : La' →+ V) (jb : Lb' →+ V),
    Unram o O' → SelfDual ha' → SelfDual hb' →
    LatModel h O La ha' io ja → LatModel h O Lb hb' io jb → IsHerm h →
    (∀ c : o, c ≠ 0 → IsUnit (io (algebraMap o O' c))) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ La) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ Lb) →
    ∀ (r : ℕ) (e : Fin r → V), (∀ i k, h (e i) (e k) = 0) → (∀ i, e i ∈ La) →
    LinearIndependent E e → (∀ c : Fin r → E, (∑ i, c i • e i) ∈ La → ∀ i, c i ∈ O) →
    (∀ v, (∀ i, h v (e i) = 0) → (v ∈ La ↔ v ∈ Lb)) →
    ∃ n : V ≃ₗ[E] V, (∀ v w, h (n v) (n w) = h v w) ∧ (∀ v, (∀ i, h v (e i) = 0) → n v = v) ∧
      ∀ v, v ∈ La ↔ n v ∈ Lb
def SatFree : Prop :=
  ∀ (o O' Lam' : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O'] [StarRing O']
    [Algebra o O'] [AddCommGroup Lam'] [Module O' Lam'] [Module.Free O' Lam'] [Module.Finite O' Lam']
    (h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O')
    (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (io : O' →+* E) (j : Lam' →+ V),
    Unram o O' → ∀ hm : LatModel h O abelian₂ h' io j,
    (∀ c : o, c ≠ 0 → IsUnit (io (algebraMap o O' c))) →
    (∀ x : E, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) * x ∈ O) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ abelian₂) →
    ∀ (m₀ : ℕ) (f : Fin m₀ → V), LinearIndependent E f →
      Satur o (capSub hm (Submodule.span E (Set.range f))) ∧
      Module.Free O' (capSub hm (Submodule.span E (Set.range f))) ∧
      Module.finrank O' (capSub hm (Submodule.span E (Set.range f))) = m₀
def PerpPerp : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Y Q : Submodule E V),
    IsHerm h → (∀ Φ : V →ₗ[E] E, ∃ v, ∀ x, Φ x = h x v) → IsCompl Y Q → Module.Projective E Q →
    ∀ v, v ∈ Y ↔ ∀ w, (∀ η ∈ Y, h w η = 0) → h w v = 0
def DualCapY : Prop :=
  ∀ (o O' Lam' : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O'] [StarRing O']
    [Algebra o O'] [AddCommGroup Lam'] [Module O' Lam'] [Module.Free O' Lam'] [Module.Finite O' Lam']
    (h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O')
    (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (io : O' →+* E) (j : Lam' →+ V),
    Unram o O' → SelfDual h' → LatModel h O abelian₂ h' io j → IsHerm h →
    (∀ c : o, c ≠ 0 → IsUnit (io (algebraMap o O' c))) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ abelian₂) →
    (∀ Φ : V →ₗ[E] E, ∃ v, ∀ x, Φ x = h x v) →
    ∀ (Y Q : Submodule E V), IsCompl Y Q → Module.Projective E Q →
    ∀ y : V, (∀ w ∈ abelian₂, (∀ η ∈ Y, h w η = 0) → h w y ∈ O) ↔ ∃ l ∈ abelian₂, y - l ∈ Y
def LevelStep : Prop :=
  ∀ (E : Type) [CommRing E] (V : Type) [AddCommGroup V] [Module E V] (O : Subring E)
    (abelian₂ : AddSubgroup V) (θ : Eˣ) (n : ℕ) (f f' : Fin n → V) (J : Fin n),
    LevelLe O abelian₂ θ f f' J.val →
    ∀ (al al' : E), ∀ l ∈ abelian₂,
      ((θ⁻¹ : Eˣ) : E) • (al • f J + al' • f' J) - l ∈ spanY E f f' J.val → InRR O (θ : E) al al'
def ChiIntegral : Prop :=
  ∀ (o O' Lam' : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O'] [StarRing O']
    [Algebra o O'] [AddCommGroup Lam'] [Module O' Lam'] [Module.Free O' Lam'] [Module.Finite O' Lam']
    (h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O')
    (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (io : O' →+* E) (j : Lam' →+ V),
    Unram o O' → SelfDual h' → LatModel h O abelian₂ h' io j → IsHerm h →
    (∀ c : o, c ≠ 0 → IsUnit (io (algebraMap o O' c))) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ abelian₂) →
    (∀ Φ : V →ₗ[E] E, ∃ v, ∀ x, Φ x = h x v) →
    ∀ (θ : Eˣ) (n : ℕ) (f f' : Fin n → V) (J : Fin n) (Q : Submodule E V),
    IsCompl (spanY E f f' J.val) Q → Module.Projective E Q → LevelLe O abelian₂ θ f f' J.val →
    ∀ al al' : E,
      (∀ u ∈ abelian₂, (∀ η ∈ spanY E f f' J.val, h u η = 0) →
        h (((θ⁻¹ : Eˣ) : E) • (al • f J + al' • f' J)) u ∈ O) →
      InRR O (θ : E) al al'
def CondPairing : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (UU : AddSubgroup V) (ψ₀ : AddChar E ℂ) (y : V),
    (∀ c ∈ O, star c ∈ O) → IsLat O UU → (∀ c : E, (∀ a ∈ O, ψ₀ (a * c) = 1) → c ∈ O) →
    (∀ u ∈ UU, ψ₀ (-(h y u)) = 1) → ∀ u ∈ UU, h y u ∈ O
def ChiNontrivial : Prop :=
  ∀ (o O' Lam' : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O'] [StarRing O']
    [Algebra o O'] [AddCommGroup Lam'] [Module O' Lam'] [Module.Free O' Lam'] [Module.Finite O' Lam']
    (h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O')
    (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (io : O' →+* E) (j : Lam' →+ V),
    Unram o O' → SelfDual h' → LatModel h O abelian₂ h' io j → IsHerm h →
    (∀ c : o, c ≠ 0 → IsUnit (io (algebraMap o O' c))) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ abelian₂) →
    (∀ Φ : V →ₗ[E] E, ∃ v, ∀ x, Φ x = h x v) →
    ∀ (θ : Eˣ) (n : ℕ) (f f' : Fin n → V) (J : Fin n) (Q : Submodule E V),
    IsCompl (spanY E f f' J.val) Q → Module.Projective E Q → LevelLe O abelian₂ θ f f' J.val →
    ∀ ψ₀ : AddChar E ℂ, (∀ c : E, (∀ a ∈ O, ψ₀ (a * c) = 1) → c ∈ O) →
    ∀ al al' : E, ¬ InRR O (θ : E) al al' →
      ∃ u ∈ abelian₂, (∀ η ∈ spanY E f f' J.val, h u η = 0) ∧
        ψ₀ (-(h (al • f J + al' • f' J) u * ((θ⁻¹ : Eˣ) : E))) ≠ 1
def CapYIndex : Prop :=
  ∀ (E : Type) [CommRing E] (V : Type) [AddCommGroup V] [Module E V] (O : Subring E)
    (abelian₂ : AddSubgroup V) (θ : Eˣ), (θ : E) ∈ O → IsLat O abelian₂ →
    ∀ (n : ℕ) (f f' : Fin n → V), LinearIndependent E (Sum.elim f f') →
    (∀ i, f i ∈ abelian₂) → (∀ i, InTh (θ : E) abelian₂ (f' i - f i)) →
    ∀ J : ℕ,
      (∀ v, (v ∈ latM O θ f f' ∧ v ∈ spanY E f f' J) ↔ v ∈ latMJ O θ f f' J) ∧
      (LevelLe O abelian₂ θ f f' J →
        (∀ v ∈ abelian₂, v ∈ Submodule.span E (Set.range f ∪ Set.range f') →
          ∃ y ∈ abelian₂, y ∈ spanY E f f' J ∧ v - y ∈ latM O θ f f') ∧
        (latMJ O θ f f' J).toAddSubgroup.relIndex (abelian₂ ⊓ (spanY E f f' J).toAddSubgroup)
          = (latM O θ f f').toAddSubgroup.relIndex
              (abelian₂ ⊓ (Submodule.span E (Set.range f ∪ Set.range f')).toAddSubgroup))
def PrimTuple (O : Type*) {abelian₂ : Type*} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] {m : ℕ}
    (x : Fin m → abelian₂) : Prop :=
  ∀ P : Ideal O, P.IsMaximal → ∀ c : Fin m → O,
    (∑ i, c i • x i) ∈ P • (⊤ : Submodule O abelian₂) → ∀ i, c i ∈ P
def GramSubmersion : Prop :=
  ∀ (o O abelian₂ : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
    [Algebra o O] [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂] [Module.Finite O abelian₂]
    (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O), Unram o O → SelfDual h →
    ∀ (m : ℕ) (x : Fin m → abelian₂), PrimTuple O x →
      (∀ c : Fin m → O, ∃ y, ∀ i, h y (x i) = c i) ∧
      ∀ H : Matrix (Fin m) (Fin m) O, (∀ i k, star (H i k) = H k i) →
        ∃ y : Fin m → abelian₂, ∀ i k, h (y i) (x k) + h (x i) (y k) = H i k
def GramLiftCount : Prop :=
  ∀ (o O abelian₂ Lb : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
    [Algebra o O] [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂] [Module.Finite O abelian₂]
    [AddCommGroup Lb] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O) (ϖ : o) (red : abelian₂ →+ Lb) (q n m t : ℕ)
    (x : Fin m → abelian₂) (Gm : Matrix (Fin m) (Fin m) O),
    Unram o O → SelfDual h → Irreducible ϖ → Nat.card (IsLocalRing.ResidueField o) = q → 2 ≤ q →
    Module.finrank O abelian₂ = n → Function.Surjective red →
    (∀ v, red v = 0 ↔ ∃ w, v = algebraMap o O ϖ • w) →
    PrimTuple O x → (∀ i k, star (Gm i k) = Gm k i) → 1 ≤ t →
    (∀ i k, algebraMap o O (ϖ ^ t) ∣ h (x i) (x k) - Gm i k) →
    Nat.card {yb : Fin m → Lb // ∃ y : Fin m → abelian₂, (∀ i, red (y i) = yb i) ∧
        ∀ i k, algebraMap o O (ϖ ^ (t + 1)) ∣
          h (x i + algebraMap o O (ϖ ^ t) • y i) (x k + algebraMap o O (ϖ ^ t) • y k) - Gm i k}
      * q ^ (m ^ 2) = q ^ (2 * n * m)
def GramSubmersionInert : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) L) (X : Fin m → Fin n → L) (Hm : Matrix (Fin m) (Fin m) L),
      IsUnit Ph.det → (∀ k l, Ph l k = Ph k l ^ Fintype.card K) → LinearIndependent L X →
      (∀ i j, Hm j i = Hm i j ^ Fintype.card K) →
      {Y : Fin m → Fin n → L | ∀ i j,
          (∑ k, ∑ l, Y i k * Ph k l * X j l ^ Fintype.card K)
            + (∑ k, ∑ l, X i k * Ph k l * Y j l ^ Fintype.card K) = Hm i j}.ncard
        * Fintype.card K ^ (m ^ 2) = Fintype.card K ^ (2 * n * m)
def GramSubmersionSplit : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) K)
    (X₁ X₂ : Fin m → Fin n → K) (Hm : Matrix (Fin m) (Fin m) K),
      IsUnit Ph.det → LinearIndependent K X₁ → LinearIndependent K X₂ →
      {Y : (Fin m → Fin n → K) × (Fin m → Fin n → K) | ∀ i j,
          (∑ k, ∑ l, Y.1 i k * Ph k l * X₂ j l) + (∑ k, ∑ l, X₁ i k * Ph k l * Y.2 j l) = Hm i j}.ncard
        * Fintype.card K ^ (m ^ 2) = Fintype.card K ^ (2 * n * m)
def NormOnto : Prop :=
  ∀ (o O : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
    [Algebra o O], Unram o O → IsAdicComplete (IsLocalRing.maximalIdeal o) o →
    Finite (IsLocalRing.ResidueField o) →
    ∀ c : o, IsUnit c → ∃ a : O, a * star a = algebraMap o O c
def SelfDualOrthonormal : Prop :=
  ∀ (o O abelian₂ : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
    [Algebra o O] [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂] [Module.Finite O abelian₂]
    (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O), Unram o O → SelfDual h →
    (∀ c : o, IsUnit c → ∃ a : O, a * star a = algebraMap o O c) →
    ∃ b : Module.Basis (Fin (Module.finrank O abelian₂)) O abelian₂, ∀ i k, h (b i) (b k) = if i = k then 1 else 0
def SelfDualOrbit : Prop :=
  ∀ (o O' : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O'] [StarRing O']
    [Algebra o O']
    (La' Lb' : Type) [AddCommGroup La'] [Module O' La'] [Module.Free O' La'] [Module.Finite O' La']
    [AddCommGroup Lb'] [Module O' Lb'] [Module.Free O' Lb'] [Module.Finite O' Lb']
    (ha' : La' →ₗ[O'] La' →ₗ⋆[O'] O') (hb' : Lb' →ₗ[O'] Lb' →ₗ⋆[O'] O')
    (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (La Lb : AddSubgroup V) (io : O' →+* E)
    (ja : La' →+ V) (jb : Lb' →+ V),
    Unram o O' → SelfDual ha' → SelfDual hb' →
    LatModel h O La ha' io ja → LatModel h O Lb hb' io jb →
    (∀ c : o, IsUnit c → ∃ a : O', a * star a = algebraMap o O' c) →
    (∀ c : o, c ≠ 0 → IsUnit (io (algebraMap o O' c))) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ La) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ Lb) →
    ∃ g : V ≃ₗ[E] V, (∀ v w, h (g v) (g w) = h v w) ∧ ∀ v, v ∈ La ↔ g v ∈ Lb
def GlueBij : Prop :=
  ∀ (o O' Lam' : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O'] [StarRing O']
    [Algebra o O'] [AddCommGroup Lam'] [Module O' Lam'] [Module.Free O' Lam'] [Module.Finite O' Lam']
    (h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O')
    (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (io : O' →+* E) (j : Lam' →+ V),
    Unram o O' → SelfDual h' → LatModel h O abelian₂ h' io j → IsHerm h →
    (∀ c : o, c ≠ 0 → IsUnit (io (algebraMap o O' c))) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ abelian₂) →
    (∀ v, (∀ w, h w v = 0) → v = 0) →
    ∀ Z Z' : Submodule E V, IsCompl Z Z' → (∀ z ∈ Z, ∀ z' ∈ Z', h z z' = 0) →
      (∀ l ∈ abelian₂, ∀ v ∈ Z, ∀ z' ∈ Z', l = v + z' → v ∈ dualIn h O abelian₂ Z ∧ (v ∈ abelian₂ → z' ∈ abelian₂)) ∧
      (∀ v ∈ dualIn h O abelian₂ Z, ∃ l ∈ abelian₂, ∃ z' ∈ Z', l = v + z') ∧
      ((abelian₂ ⊓ Z.toAddSubgroup) ⊔ (abelian₂ ⊓ Z'.toAddSubgroup)).relIndex abelian₂
        = (abelian₂ ⊓ Z.toAddSubgroup).relIndex (dualIn h O abelian₂ Z)
def StTrivial : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (X X' ME : Submodule E V) (g : V →ₗ[E] V),
    X ⊓ X' = ⊥ → X ≤ ME → X' ≤ ME →
    (∀ v, (∀ x ∈ X, h v x = 0) → g v - v ∈ X) → (∀ v, (∀ x ∈ X', h v x = 0) → g v - v ∈ X') →
    (∀ w, (∀ z ∈ ME, h w z = 0) → g w = w) ∧
    ((∀ v, ∃ z ∈ ME, ∀ z' ∈ ME, h (v - z) z' = 0) → (∀ z ∈ ME, g z = z) → ∀ v, g v = v)
end Formalism.HermitianLatticeCounting.S4


