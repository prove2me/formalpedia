-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:34.256503+00:00
-- url     : https://prove2.me/theorems/cf6ecf24-15f2-4cbd-878b-b131b43ef1b8
-- title:
--   Minor Ordered Entries
-- statement:
--   Definitions and structural lemmas for Minor Ordered Entries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/MinorOrderedEntries.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open scoped TensorProduct Kronecker
namespace GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
variable {ι : Type} [Fintype ι] [DecidableEq ι]
abbrev UG (ι : Type) (n : ℕ) : Type := ι → Matrix.unitaryGroup (Fin n) ℂ
def linSub {σ : Type} [Fintype σ] [DecidableEq σ] :
    (ι → Matrix σ σ ℂ) →* Module.End ℂ (MvPolynomial (ι × σ) ℂ) where
  toFun M := (aeval (R := ℂ) fun p : ι × σ => ∑ j, C (M p.1 j p.2) * (X (p.1, j) : MvPolynomial (ι × σ) ℂ)).toLinearMap
  map_one' := by
    have : (aeval (R := ℂ) fun p : ι × σ => ∑ j, C ((1 : ι → Matrix σ σ ℂ) p.1 j p.2) * (X (p.1, j) : MvPolynomial (ι × σ) ℂ))
        = AlgHom.id ℂ _ := by
      ext1 p
      simp [Matrix.one_apply, apply_ite C]
    rw [this]; rfl
  map_mul' M N := by
    have : (aeval (R := ℂ) fun p : ι × σ => ∑ j, C ((M * N) p.1 j p.2) * (X (p.1, j) : MvPolynomial (ι × σ) ℂ))
        = (aeval (R := ℂ) fun p : ι × σ => ∑ j, C (M p.1 j p.2) * (X (p.1, j) : MvPolynomial (ι × σ) ℂ)).comp
          (aeval (R := ℂ) fun p : ι × σ => ∑ j, C (N p.1 j p.2) * (X (p.1, j) : MvPolynomial (ι × σ) ℂ)) := by
      ext1 p
      simp only [aeval_X, AlgHom.comp_apply, map_sum, map_mul, aeval_C, algebraMap_eq, Pi.mul_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [this]; rfl
def detU (n : ℕ) : Matrix.unitaryGroup (Fin n) ℂ →* ℂˣ :=
  ((Matrix.detMonoidHom (n := Fin n) (R := ℂ)).comp (Matrix.unitaryGroup (Fin n) ℂ).subtype).toHomUnits
def detChar (n : ℕ) (k : ι → ℤ) : UG ι n →* ℂˣ where
  toFun g := ∏ τ, detU n (g τ) ^ k τ
  map_one' := by simp
  map_mul' g h := by simp [mul_zpow, Finset.prod_mul_distrib]
def twist {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (χ : G →* ℂˣ) (ρ : Representation ℂ G V) :
    Representation ℂ G V where
  toFun g := (χ g : ℂ) • ρ g
  map_one' := by simp
  map_mul' g h := by simp [mul_smul, smul_comm (χ h : ℂ) (χ g : ℂ)]
abbrev Pol (ι : Type) (a b : ℕ) : Type := MvPolynomial (ι × Fin b × Fin a) ℂ
def homMat (a b : ℕ) : UG ι a × UG ι b →* (ι → Matrix (Fin b × Fin a) (Fin b × Fin a) ℂ) where
  toFun x τ := (x.2 τ).1 ⊗ₖ (star (x.1 τ).1)ᵀ
  map_one' := by funext τ; simp
  map_mul' x y := by
    funext τ
    simp [Matrix.mul_kronecker_mul, star_mul, Matrix.transpose_mul]
def fock (a b : ℕ) (α β : ι → ℤ) : Representation ℂ (UG ι a × UG ι b) (Pol ι a b) :=
  twist ((detChar a α).comp (MonoidHom.fst _ _) * (detChar b β).comp (MonoidHom.snd _ _)) (linSub.comp (homMat a b))
def leftRep (n : ℕ) : Representation ℂ (UG ι n) (Pol ι n n) :=
  (linSub.comp (homMat n n)).comp (MonoidHom.inr _ _)
def minor (n : ℕ) (τ : ι) (l : Fin n) : Pol ι n n :=
  (Matrix.of fun p q : Fin (l + 1) => (X (τ, Fin.castLE l.2 p, Fin.castLE l.2 q) : Pol ι n n)).det
def hwVec (n : ℕ) (lam : ι → ℕ → ℤ) : Pol ι n n :=
  ∏ τ, ∏ l ∈ Finset.univ.filter (fun l : Fin n => l.1 + 1 < n), minor n τ l ^ (lam τ l - lam τ (l + 1)).toNat
def weylSub (n : ℕ) (lam : ι → ℕ → ℤ) : Submodule ℂ (Pol ι n n) :=
  Submodule.span ℂ (Set.range fun g : UG ι n => leftRep n g (hwVec n lam))
theorem span_orbit_le {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) (g : G) :
    Submodule.span ℂ (Set.range fun h : G => ρ h v) ≤ (Submodule.span ℂ (Set.range fun h : G => ρ h v)).comap (ρ g) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, rfl⟩
  refine Submodule.subset_span ⟨g * h, ?_⟩
  simp
theorem weylSub_le (n : ℕ) (lam : ι → ℕ → ℤ) (g : UG ι n) : weylSub n lam ≤ (weylSub n lam).comap (leftRep n g) :=
  span_orbit_le (leftRep n) (hwVec n lam) g
def weylRep (n : ℕ) (lam : ι → ℕ → ℤ) : Representation ℂ (UG ι n) (weylSub n lam) :=
  twist (detChar n fun τ => lam τ (n - 1)) (Representation.subrepresentation (leftRep n) (weylSub n lam) (weylSub_le n lam))
def hw (p : List ℚ) (i : ℕ) : ℤ := ⌊p.getD i 0 - (((p.length : ℚ) - 1) / 2 - i)⌋
def block (x : ℚ) (n : ℕ) : List ℚ := (List.range n).map fun i : ℕ => x + ((n : ℚ) - 1) / 2 - i
structure Sizes where
  k : ℕ
  m : ℕ
  s : ℕ
  t : ℕ
  k_pos : 0 < k
  k_even : Even k
  m_pos : 0 < m
  m_even : Even m
  s_odd : Odd s
  t_odd : Odd t
structure Entries (S : Sizes) where
  a : Fin (S.m + 1) → ℚ
  c : Fin S.m → ℤ
  v : Fin (S.k - 1) → ℤ
  u : Fin (S.k - 1) → ℚ
  b : Fin S.m → ℤ
  e : Fin S.m → ℤ
namespace Entries
variable {S : Sizes} (P : Entries S)
def orderList : List ℚ :=
  P.a 0 :: ((List.finRange S.m).flatMap fun i => block (P.c i) S.s ++ [P.a i.succ]) ++
    ((List.finRange (S.k - 1)).flatMap fun i => [(P.v i : ℚ), P.u i]) ++
    ((List.finRange S.m).flatMap fun j => (-P.b j : ℚ) :: block (-P.e j) S.t)
structure Good : Prop where
  a_half : ∀ l, ∃ z : ℤ, P.a l = z + 1 / 2
  u_half : ∀ i, ∃ z : ℤ, P.u i = z + 1 / 2
  order : P.orderList.Pairwise (· > ·)
def psiPar : List ℚ :=
  P.a 0 :: ((List.finRange S.m).flatMap fun i => block (P.c i) (S.s - 1) ++ [P.a i.succ]) ++ (List.finRange (S.k - 1)).map P.u
def bigPar : List ℚ := P.psiPar ++ (List.finRange S.m).flatMap fun j => block (-P.e j) (S.t + 1)
def basePar : List ℚ :=
  (List.finRange (S.k - 1)).map (fun i => (P.v i : ℚ)) ++
    (List.finRange S.m).flatMap fun j => (-P.b j : ℚ) :: block (-P.e j) S.t
def smallPar : List ℚ := ((List.finRange S.m).flatMap fun i => block (P.c i) S.s) ++ P.basePar
end Entries
namespace Sizes
variable (S : Sizes)
def nR (j : ℕ) : ℕ := S.k + S.m * S.s + j * (S.t + 1)
def nC (i : ℕ) : ℕ := S.k + S.m - 1 + S.m * S.t + i * S.s
theorem nC_succ : S.nC S.m + 1 = S.nR S.m := by
  have := S.k_pos
  unfold nC nR
  rw [mul_add, mul_one]; omega
end Sizes
def embedE {n N : ℕ} (e : Fin n ⊕ Fin 1 ≃ Fin N) : Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin N) ℂ where
  toFun y := ⟨Matrix.reindex e e (Matrix.fromBlocks y.1 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)), by
    rw [Matrix.mem_unitaryGroup_iff]
    have hy : y.1 * (y.1)ᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 y.2
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hy]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' y z := by
    apply Subtype.ext
    simp [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
def embed1 {n N : ℕ} (h : n + 1 = N) : Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin N) ℂ :=
  embedE (finSumFinEquiv.trans (finCongr h))
def embed {n N : ℕ} (h : n + 1 = N) : UG ι n →* UG ι N := MonoidHom.compLeft (embed1 h) ι
abbrev Gc (ι : Type) (S : Sizes) : Type := (∀ j : Fin S.m, UG ι (S.nR j)) × (∀ i : Fin (S.m + 1), UG ι (S.nC i))
def rowComp (S : Sizes) : Gc ι S →* ∀ j : Fin (S.m + 1), UG ι (S.nR j) where
  toFun g := Fin.snoc (α := fun j : Fin (S.m + 1) => UG ι (S.nR j)) g.1 (embed S.nC_succ (g.2 (Fin.last _)))
  map_one' := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Fin.snoc_last]; exact map_one _
    · rw [Fin.snoc_castSucc]; rfl
  map_mul' g h := by
    funext j
    rw [Pi.mul_apply]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Fin.snoc_last, Fin.snoc_last, Fin.snoc_last]; exact map_mul _ _ _
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
variable {S : Sizes} (P : ι → Entries S)
def rowFock (j : Fin S.m) : Representation ℂ (Gc ι S) (Pol ι (S.nR j.castSucc) (S.nR j.succ)) :=
  (fock _ _ (fun τ => (P τ).e j - (S.nR j.succ / 2 : ℕ)) (fun τ => -(P τ).e j + (S.nR j.castSucc / 2 : ℕ))).comp
    (((Pi.evalMonoidHom _ j.castSucc).prod (Pi.evalMonoidHom _ j.succ)).comp (rowComp S))
def colFock (i : Fin S.m) : Representation ℂ (Gc ι S) (Pol ι (S.nC i.castSucc) (S.nC i.succ)) :=
  (fock _ _ (fun τ => (P τ).c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (fun τ => -(P τ).c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ))).comp
    (((Pi.evalMonoidHom _ i.castSucc).prod (Pi.evalMonoidHom _ i.succ)).comp (MonoidHom.snd _ _))
def piTprod {G J : Type} [Monoid G] {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (ρ : ∀ j, Representation ℂ G (V j)) : Representation ℂ G (⨂[ℂ] j, V j) :=
  PiTensorProduct.mapMonoidHom.comp (Pi.monoidHom ρ)
def psiWt (τ : ι) : ℕ → ℤ := hw (P τ).psiPar
def baseWt (τ : ι) : ℕ → ℤ := hw (P τ).basePar
def psiRep : Representation ℂ (Gc ι S) (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P)) :=
  (weylRep _ (psiWt P)).comp ((Pi.evalMonoidHom _ 0).comp (rowComp S))
def baseRep : Representation ℂ (Gc ι S) (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) :=
  (weylRep _ (baseWt P)).comp ((Pi.evalMonoidHom _ 0).comp (MonoidHom.snd _ _))
abbrev OM : Type :=
  (⨂[ℂ] j : Fin S.m, Pol ι (S.nR j.castSucc) (S.nR j.succ)) ⊗[ℂ]
    ((⨂[ℂ] i : Fin S.m, Pol ι (S.nC i.castSucc) (S.nC i.succ)) ⊗[ℂ]
      (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) ⊗[ℂ] Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P))))
def omRep : Representation ℂ (Gc ι S) (OM P) :=
  (piTprod (rowFock P)).tprod ((piTprod (colFock P)).tprod ((psiRep P).tprod (baseRep P).dual))
def invFun {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Submodule ℂ (Module.Dual ℂ V) where
  carrier := {l | ∀ g x, l (ρ g x) = l x}
  add_mem' h h' g x := by simp [h g x, h' g x]
  zero_mem' _ _ := rfl
  smul_mem' c _ h g x := by simp [h g x]
def intertw {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') : Submodule ℂ (V →ₗ[ℂ] V') where
  carrier := {f | ∀ g x, f (ρ g x) = ρ' g (f x)}
  add_mem' h h' g x := by simp [h g x, h' g x]
  zero_mem' _ _ := by simp
  smul_mem' c _ h g x := by simp [h g x]
def Interlace (big small : List ℚ) : Prop :=
  big.length = small.length + 1 ∧ ∀ i (h : i < small.length) (h' : i + 1 < big.length), big[i] > small[i] ∧ small[i] > big[i + 1]
def Interlacing : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Sizes) (P : ι → Entries S), (∀ τ, (P τ).Good) →
    (∀ τ, Interlace (P τ).bigPar (P τ).smallPar) ∧
      Module.finrank ℂ (intertw (weylRep (S.nC S.m) fun τ => hw (P τ).smallPar)
        ((weylRep (S.nR S.m) fun τ => hw (P τ).bigPar).comp (embed S.nC_succ))) = 1
def OneLine : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Sizes) (P : ι → Entries S), (∀ τ, (P τ).Good) →
    Module.finrank ℂ (invFun (omRep P)) = 1
abbrev exSizes : Sizes := ⟨2, 2, 3, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩
def exEntries : Entries exSizes := ⟨![23 / 2, 13 / 2, 5 / 2], ![8, 4], ![1], ![1 / 2], ![1, 5], ![3, 7]⟩
example : exEntries.bigPar = [23 / 2, 17 / 2, 15 / 2, 13 / 2, 9 / 2, 7 / 2, 5 / 2, 1 / 2, -5 / 2, -7 / 2, -13 / 2, -15 / 2] ∧
    exEntries.smallPar = [9, 8, 7, 5, 4, 3, 1, -1, -3, -5, -7] := by decide +kernel
end GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries


