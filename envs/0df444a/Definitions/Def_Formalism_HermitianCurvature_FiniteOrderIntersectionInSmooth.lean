-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
-- name    : Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:09:57.338921+00:00
-- url     : https://prove2.me/theorems/2b6521f4-6169-4c8f-bd72-3aca3b419034
-- title:
--   Finite Order Intersection In Smooth
-- statement:
--   Definitions and structural lemmas for Finite Order Intersection In Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/FiniteOrderIntersectionInSmooth.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.C2
open Formalism.QuantumDeterminants
def mx {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) : ℝ := ‖Matrix.of.symm M‖
def UTset (m : ℕ) : Set (Matrix (Fin m) (Fin m) ℂ) := {u | (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1}
def LTset (m : ℕ) : Set (Matrix (Fin m) (Fin m) ℂ) := {l | (∀ i j, i < j → l i j = 0) ∧ ∀ i, l i i = 1}
def monoP {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i a => if i = w a then d a else 0
def IsMonomial {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) ∧ P = monoP w d
def Eij {m : ℕ} (p q : Fin m) (c : ℂ) : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => if i = p ∧ j = q then c else 0
def antiW (s : ℕ) : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun i j => if j = i.rev then 1 else 0
def simpleLow {m : ℕ} (l : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ∑ a : Fin m, if h : a.val + 1 < m then l ⟨a.val + 1, h⟩ a else 0
def simpleUp {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ∑ a : Fin m, if h : a.val + 1 < m then u a ⟨a.val + 1, h⟩ else 0
def psiC (c x : ℂ) : ℂ := Complex.exp (Complex.I * ((c * x).re : ℂ))
def LPg {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {l | l ∈ LTset m ∧ P⁻¹ * l * P ∈ LTset m}
def Lstg {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {l | l ∈ LTset m ∧ P⁻¹ * l * P ∈ UTset m}
def lowOf {m : ℕ} {ι : Type*} [Fintype ι] (pos : ι → Fin m × Fin m) (v : ι → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 + Matrix.of fun i j => ∑ q, if pos q = (i, j) then v q else 0
abbrev Lidx (m : ℕ) : Type := {q : Fin m × Fin m // q.2 < q.1}
abbrev LPidx {m : ℕ} (w : Equiv.Perm (Fin m)) : Type := {q : Fin m × Fin m // q.2 < q.1 ∧ w.symm q.2 < w.symm q.1}
abbrev Lstidx {m : ℕ} (w : Equiv.Perm (Fin m)) : Type := {q : Fin m × Fin m // q.2 < q.1 ∧ w.symm q.1 < w.symm q.2}
def minorS {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (I J : Finset (Fin m)) : ℂ :=
  if h : I.card = J.card then (M.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h.symm)).det else 0
def iSet (m a : ℕ) : Finset (Fin m) := Finset.univ.filter fun i => i.val < a
def wSet {m : ℕ} (w : Equiv.Perm (Fin m)) (a : ℕ) : Finset (Fin m) := (iSet m a).image w
def IsPolyDeg {n : ℕ} (D : ℕ) (P : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, q.totalDegree ≤ D ∧
    ∀ g, P g = MvPolynomial.eval (Sum.elim (fun p => g p.1 p.2) (fun p => conj (g p.1 p.2))) q
def StdZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Prop := inWb k r z ∧ 0 < Tz k r z
def Std (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Prop := 1 ≤ k ∧ StdZ k r z ∧ StdZ k r z'
def uMap (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s : B.Mat k r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun a b => if h : a.val < r then herm (Hpk k r) (s *ᵥ fvec k r z b) (bvec (esI k r ⟨a.val, h⟩))
    else herm (Hpk k r) (s *ᵥ fvec k r z b) z / herm (Hpk k r) z z
def flagSpan (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun b : {b : Fin (r + 1) // b < a} => fvec k r z b.1)
def FlagStab (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {s | s ∈ B.GV k r ∧ ∀ a, s *ᵥ fvec k r z a - fvec k r z a ∈ flagSpan k r z a}
def CurvatureSupportSet (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) := {s | s ∈ Sset k r z ∧ uMap k r z s = 1}
def N0set (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) := {n | n ∈ Nset k r ∧ uMap k r z n = 1}
def FixSet (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ∀ a, g *ᵥ fvec k r z a = fvec k r z a}
def Adiag (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.diagonal fun a => if a = Fin.last r then -((Tz k r z : ℝ) : ℂ) else 0
def SFlag : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → FlagStab k r z = Sset k r z
def UMapFrame : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z →
    (∀ s ∈ Sset k r z, (∀ b, s *ᵥ fvec k r z b = ∑ a, uMap k r z s a b • fvec k r z a) ∧
      uMap k r z s ∈ UTset (r + 1) ∧
      ∀ t ∈ Sset k r z, uMap k r z (s * t) = uMap k r z s * uMap k r z t) ∧
    ∀ h ∈ UWset k r z, uMap k r z h = 1
def ZhatEquiv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), StdZ k r z → StdZ k r z' →
    ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ g : B.Mat k r,
      Zhat k r z z' (s⁻¹ * g * s') = (uMap k r z s)ᴴ * Zhat k r z z' g * uMap k r z' s'
def GramBlocks : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), StdZ k r z → StdZ k r z' → ∀ g ∈ B.GV k r,
    gramM k r z z' g = Matrix.fromBlocks (Adiag k r z) (Zhat k r z z' g) (Zhat k r z z' g)ᴴ (Adiag k r z')
def DetNonzero : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), StdZ k r z → StdZ k r z' → ∀ g : B.Mat k r,
    0 < Gf k r z z' g → (Zhat k r z z' g).det ≠ 0
def Majorant : Prop :=
  ∀ k r : ℕ, Hpk k r ∈ B.GV k r ∧ Hpk k r * Hpk k r = 1 ∧
    ∀ v : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) v (Hpk k r *ᵥ v) = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) ∧
      (herm (Hpk k r) v v).re ≤ ∑ i, Complex.normSq (v i)
def NormInv : Prop := ∀ (k r : ℕ), ∀ g ∈ B.GV k r, B.gN g⁻¹ = B.gN g ∧ 1 ≤ B.gN g
def TwoSided : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (m : ℕ) (F : B.Mat k r → E) (c : ℝ),
    B.CkOn (m : ℕ∞) (B.GV k r) F →
    (∀ v : List (B.Mat k r), (∀ X ∈ v, B.unitLie k r X) → v.length ≤ m →
      ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.Rw v F g‖ ≤ c) →
    B.InCC (A - 2 * m) m F
def B0 (r : ℕ) : ℝ := 3 * ((r : ℝ) + 1)
def CCsc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (A : ℝ) (F : B.Mat k r → E) : Prop :=
  B.CkOn (⊤ : ℕ∞) (B.GV k r) F ∧
  ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
    ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ (A - B0 r * ((u.length : ℝ) + v.length)) * ‖B.dLR u v F g‖ ≤ C
def FiniteOrderIntersectionInSmooth : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F : B.Mat k r → E),
    (∀ m : ℕ, B.InCC A m F) → CCsc k r A F
def SmoothClassInFiniteOrder : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F : B.Mat k r → E),
    CCsc k r A F → ∀ m : ℕ, B.InCC (A - B0 r * m) m F
def RuleB : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F : B.Mat k r → E),
    CCsc k r A F → ∀ X : B.Mat k r, B.unitLie k r X →
      CCsc k r (A - B0 r) (Formalism.REAL.RdV X F) ∧ CCsc k r (A - B0 r) (B.LdV X F)
def RuleC : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F : B.Mat k r → E)
    (D : ℕ) (P : B.Mat k r → ℂ), CCsc k r A F → IsPolyDeg D P → CCsc k r (A - D) (fun g => P g • F g)
def Uperp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.ker (Matrix.mulVecLin ((Matrix.of fun i j => star (gramVec k r z z' γ i j)) * Hpk k r))
def KU (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ∀ i, g *ᵥ gramVec k r z z' γ i = gramVec k r z z' γ i}
def Hst (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Set (B.Mat k r) :=
  {g | g ∈ Sset k r z ∧ ∃ s' ∈ Sset k r z', g = γ * s' * γ⁻¹}
def Rst (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Set (B.Mat k r) :=
  {g | g ∈ Hst k r z z' γ ∧ ∀ v ∈ Uperp k r z z' γ, g *ᵥ v = v}
def PosPt (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Prop :=
  γ ∈ B.GV k r ∧ 0 < Gf k r z z' γ
def GramIndependentSignature : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    LinearIndependent ℂ (gramVec k r z z' γ) ∧
    (∃ Q : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ, IsUnit Q.det ∧
      Qᴴ * gramM k r z z' γ * Q = Matrix.fromBlocks 1 0 0 (-1)) ∧
    (∀ v ∈ Uperp k r z z' γ, v ≠ 0 → 0 < (herm (Hpk k r) v v).re) ∧
    Module.finrank ℂ (Uperp k r z z' γ) = k - 1
def C1ii : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    KU k r z z' γ ⊆ Hst k r z z' γ ∧
    Rst k r z z' γ = {g | g ∈ Nset k r ∧ ∃ n ∈ Nset k r, g = γ * n * γ⁻¹} ∧
    (∀ h ∈ Hst k r z z' γ, ∃! p : B.Mat k r × B.Mat k r,
      p.1 ∈ Rst k r z z' γ ∧ p.2 ∈ KU k r z z' γ ∧ h = p.1 * p.2) ∧
    (∀ ρ ∈ Rst k r z z' γ, ∀ κ ∈ KU k r z z' γ, ρ * κ = κ * ρ) ∧
    ∀ ρ ∈ Rst k r z z' γ, (ρ - 1) ^ (2 * r + k + 1) = 0
def CurvatureConditionOneClauseThree : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    Set.BijOn (fun ρ => (uMap k r z ρ, uMap k r z' (γ⁻¹ * ρ * γ))) (Rst k r z z' γ)
      {p | p.1 ∈ UTset (r + 1) ∧ p.2 ∈ UTset (r + 1) ∧ p.1ᴴ * Zhat k r z z' γ * p.2 = Zhat k r z z' γ} ∧
    Set.InjOn (uMap k r z) (Rst k r z z' γ) ∧
    Set.InjOn (fun ρ => uMap k r z' (γ⁻¹ * ρ * γ)) (Rst k r z z' γ)
def C1iv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    {p : B.Mat k r × B.Mat k r | p.1 ∈ Sset k r z ∧ p.2 ∈ Sset k r z' ∧ p.1⁻¹ * γ * p.2 = γ} =
      (fun g => (g, γ⁻¹ * g * γ)) '' Hst k r z z' γ
def RelevantPair : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) →
    ∀ a b : Fin m, a < b → w b < w a → ∀ x : ℂ,
      (1 + Eij (w a) (w b) (-(x * d a / d b))) ∈ LTset m ∧ (1 + Eij a b x) ∈ UTset m ∧
      (1 + Eij (w a) (w b) (-(x * d a / d b))) * monoP w d * (1 + Eij a b x) = monoP w d ∧
      simpleLow (1 + Eij (w a) (w b) (-(x * d a / d b))) + simpleUp (1 + Eij a b x) =
        (if b.val = a.val + 1 then x else 0) - (if (w a).val = (w b).val + 1 then x * d a / d b else 0)
def RelevantTriv : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (c : ℂ), (∀ a, d a ≠ 0) → c ≠ 0 →
    ∀ a b : Fin m, a < b → w b < w a →
      ((∀ x : ℂ, psiC c ((if b.val = a.val + 1 then x else 0) -
          (if (w a).val = (w b).val + 1 then x * d a / d b else 0)) = 1) ↔
        ((b.val = a.val + 1 ↔ (w a).val = (w b).val + 1) ∧ (b.val = a.val + 1 → d a = d b)))
def RelevantCrit : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ),
    (∀ a b : Fin m, a < b → w b < w a →
      ((b.val = a.val + 1 ↔ (w a).val = (w b).val + 1) ∧ (b.val = a.val + 1 → d a = d b))) ↔
    ∃ blk : Fin m → ℕ, Monotone blk ∧ (∀ a, blk (w a) = blk a) ∧
      (∀ a b, blk a = blk b → a < b → w b < w a) ∧ (∀ a b, blk a = blk b → d a = d b)
def InvStarSub : Prop :=
  ∀ (m : ℕ) (u : Matrix (Fin m) (Fin m) ℂ), u ∈ UTset m → ∀ (a : Fin m) (h : a.val + 1 < m),
    (u⁻¹)ᴴ ⟨a.val + 1, h⟩ a = -conj (u a ⟨a.val + 1, h⟩)
def PsiNegConj : Prop := ∀ x : ℂ, psiC cStd (-conj x) = psiC cStd x
def StabAntidiag : Prop :=
  ∀ (s : ℕ) (u : Matrix (Fin s) (Fin s) ℂ) (t : ℂ), u ∈ UTset s → t ≠ 0 →
    antiW s * u⁻¹ * antiW s ∈ LTset s ∧
    (antiW s * u⁻¹ * antiW s) * (t • antiW s) * u = t • antiW s ∧
    simpleLow (antiW s * u⁻¹ * antiW s) + simpleUp u = 0
def RelevantMono : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (c : ℂ), (∀ a, d a ≠ 0) → c ≠ 0 →
    ((∀ l ∈ LTset m, ∀ u' ∈ UTset m, l * monoP w d * u' = monoP w d → psiC c (simpleLow l + simpleUp u') = 1) ↔
      ∃ blk : Fin m → ℕ, Monotone blk ∧ (∀ a, blk (w a) = blk a) ∧
        (∀ a b, blk a = blk b → a < b → w b < w a) ∧ (∀ a b, blk a = blk b → d a = d b))
def RelevantMonoOfParts : Prop := RelevantPair → RelevantTriv → RelevantCrit → StabAntidiag → RelevantMono
def LowSplit : Prop :=
  ∀ (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ), IsMonomial P → ∀ l ∈ LTset m,
    ∃! p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ, p.1 ∈ LPg P ∧ p.2 ∈ Lstg P ∧ l = p.1 * p.2
def LPCoords : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) →
    (Set.range (lowOf (fun q : LPidx w => q.1)) = LPg (monoP w d)) ∧
    (Set.range (lowOf (fun q : Lstidx w => q.1)) = Lstg (monoP w d))
def LowSplitMeas : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)),
    MeasurePreserving (fun p : (LPidx w → ℂ) × (Lstidx w → ℂ) => fun q : Lidx m =>
        (lowOf (fun q : LPidx w => q.1) p.1 * lowOf (fun q : Lstidx w => q.1) p.2) q.1.1 q.1.2)
      volume volume
def URImage : Prop :=
  ∀ (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ), IsMonomial P →
    {u | u ∈ UTset m ∧ ∃ u' ∈ UTset m, uᴴ * P * u' = P} = {u | u ∈ UTset m ∧ uᴴ ∈ Lstg P}
def UpSplit : Prop :=
  ∀ (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ), IsMonomial P → ∀ u ∈ UTset m,
    ∃! p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ,
      p.1 ∈ UTset m ∧ p.2 ∈ UTset m ∧ p.1ᴴ ∈ Lstg P ∧ p.2ᴴ ∈ LPg P ∧ u = p.1 * p.2
def UpSplitOfLowSplit : Prop := LowSplit → UpSplit
def MinorU : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) → ∀ a b : Fin m, a < b →
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ l ∈ LPg (monoP w d), ∀ u' ∈ UTset m,
      u' a b * minorS (monoP w d) (wSet w (a.val + 1)) (iSet m (a.val + 1)) =
        ε * minorS (l * monoP w d * u') (wSet w (a.val + 1)) (insert b (iSet m a.val))
def MinorL : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) → ∀ (a i : Fin m), i ∉ wSet w a.val →
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ l ∈ LPg (monoP w d), ∀ u' ∈ UTset m,
      l i (w a) * minorS (monoP w d) (wSet w (a.val + 1)) (iSet m (a.val + 1)) =
        ε * minorS (l * monoP w d * u') (insert i (wSet w a.val)) (iSet m (a.val + 1))
def MinorCNonzero : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) → ∀ a ≤ m,
    minorS (monoP w d) (wSet w a) (iSet m a) ≠ 0
def MonomialFactorizationBound : Prop :=
  ∀ (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ), IsMonomial P → ∃ C : ℝ, ∀ l ∈ LPg P, ∀ u' ∈ UTset m,
    mx l ≤ C * (1 + mx (l * P * u')) ^ m ∧ mx u' ≤ C * (1 + mx (l * P * u')) ^ m ∧
    mx l⁻¹ ≤ C * (1 + mx (l * P * u')) ^ ((m - 1) * m) ∧ mx u'⁻¹ ≤ C * (1 + mx (l * P * u')) ^ ((m - 1) * m)
def xiV (k r : ℕ) (ξ : Fin r → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i => if h : i.val < r then ξ ⟨i.val, h⟩ else 0
def nEich (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ) : B.Mat k r :=
  1 + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) •
    (-(vecMulVec (xiV k r ξ) (star (Hpk k r *ᵥ z))) + vecMulVec z (star (Hpk k r *ᵥ xiV k r ξ)) +
      (1 / 2 : ℂ) • vecMulVec (xiV k r ξ) (star (Hpk k r *ᵥ xiV k r ξ)))
def mX (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) : B.Mat k r := fun i j =>
  if hi : i.val < r then (if hj : j.val < r then vX ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
  else if hi' : r + k < i.val then
    (if hj' : r + k < j.val then (vXᴴ)⁻¹ ⟨2 * r + k - i.val, by omega⟩ ⟨2 * r + k - j.val, by omega⟩ else 0)
  else if i = j then 1 else 0
def tauM (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : B.Mat k r :=
  nEich k r z (fun a => v a.castSucc (Fin.last r)) * mX k r (v.submatrix Fin.castSucc Fin.castSucc)
def TauMem : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → ∀ v ∈ UTset (r + 1),
    tauM k r z v ∈ Nset k r ∧ (∀ b, tauM k r z v *ᵥ fvec k r z b = ∑ a, v a b • fvec k r z a) ∧
    uMap k r z (tauM k r z v) = v
def TauBound : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → ∃ C : ℝ, ∀ v ∈ UTset (r + 1),
    B.gN (tauM k r z v) ≤ C * (1 + mx v) ^ (2 * r + 2) ∧ B.gN (tauM k r z v)⁻¹ ≤ C * (1 + mx v) ^ (2 * r + 2)
def Sg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Set (B.Mat k r) :=
  {σ | ∃ n0 ∈ N0set k r z, ∃ v ∈ UTset (r + 1), vᴴ ∈ LPg (Zhat k r z z' γ) ∧ ∃ h ∈ UWset k r z,
    σ = n0 * tauM k r z v * h}
def Sg' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) : Set (B.Mat k r) :=
  {σ | ∃ n0 ∈ N0set k r z', ∃ v ∈ UTset (r + 1),
    Zhat k r z z' γ * v * (Zhat k r z z' γ)⁻¹ ∈ UTset (r + 1) ∧ ∃ h ∈ UWset k r z', σ = n0 * tauM k r z' v * h}
def SectionDecomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    IsMonomial (Zhat k r z z' γ) → ∀ s ∈ Sset k r z,
      ∃! p : B.Mat k r × B.Mat k r, p.1 ∈ Rst k r z z' γ ∧ p.2 ∈ Sg k r z z' γ ∧ s = p.1 * p.2
def MirrorDecomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    IsMonomial (Zhat k r z z' γ) → ∀ s' ∈ Sset k r z',
      ∃! p : B.Mat k r × B.Mat k r, p.1 ∈ Rst k r z z' γ ∧ p.2 ∈ Sg' k r z z' γ ∧ s' = γ⁻¹ * p.1 * γ * p.2
def SectionDecompOfParts : Prop :=
  C1ii → CurvatureConditionOneClauseThree → URImage → UpSplit → SFlag → UMapFrame → ZhatEquiv → TauMem → SectionDecomp
def ZhatSection : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' →
    ∀ n0 ∈ N0set k r z, ∀ v ∈ UTset (r + 1), ∀ h ∈ UWset k r z, ∀ s' ∈ Sset k r z',
      Zhat k r z z' ((n0 * tauM k r z v * h)⁻¹ * γ * s') = vᴴ * Zhat k r z z' γ * uMap k r z' s'
def ZhatSectionOfParts : Prop := ZhatEquiv → UMapFrame → TauMem → SFlag → ZhatSection
def ZhatBound : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), ∃ C : ℝ, ∀ g : B.Mat k r, mx (Zhat k r z z' g) ≤ C * B.gN g
def ProjClaim : Prop :=
  ∀ (n : ℕ) (H P : Matrix (Fin n) (Fin n) ℂ) (U : Submodule ℂ (Fin n → ℂ)) (c : ℝ),
    Hᴴ = H → H * H = 1 → (∀ v ∈ U, v ≠ 0 → 0 < (herm H v v).re) →
    (∀ x, P *ᵥ x ∈ U) → (∀ x, ∀ u ∈ U, herm H (x - P *ᵥ x) u = 0) →
    0 ≤ c → (∀ x, ∑ i, Complex.normSq ((P *ᵥ x) i) ≤ c ^ 2 * ∑ i, Complex.normSq (x i)) →
    ∀ v ∈ U, ∑ i, Complex.normSq (v i) ≤ c * (herm H v v).re
def PolyProper : Prop :=
  ∃ c₁ : ℕ, ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    IsMonomial (Zhat k r z z' γ) → ∃ C : ℝ,
      (∀ σ ∈ Sg k r z z' γ, ∀ s' ∈ Sset k r z',
        B.gN σ + B.gN s' ≤ C * B.gN (σ⁻¹ * γ * s') ^ (c₁ * (r + 1) ^ 2)) ∧
      (∀ s ∈ Sset k r z, ∀ σ' ∈ Sg' k r z z' γ,
        B.gN s + B.gN σ' ≤ C * B.gN (s⁻¹ * γ * σ') ^ (c₁ * (r + 1) ^ 2))
def SliceThresholdBound : Prop :=
  ∀ (c c₃ Astar a₁ : ℝ) (r n : ℕ), 0 ≤ c₃ → c₃ ≤ c → 1 ≤ n → (n : ℝ) ^ 3 ≤ Astar →
    c * ((r : ℝ) + 1) ^ 3 * Astar ≤ a₁ → c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1) ≤ a₁
def FixFrame : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), StdZ k r z → FixSet k r z = CurvatureSupportSet k r z
def WittExt : Prop :=
  ∀ (k r : ℕ) (ι : Type) [Fintype ι] (x y : ι → Fin (2 * r + k + 1) → ℂ),
    LinearIndependent ℂ x → LinearIndependent ℂ y →
    (∀ i j, herm (Hpk k r) (x i) (x j) = herm (Hpk k r) (y i) (y j)) →
    ∃ g ∈ B.GV k r, ∀ i, g *ᵥ x i = y i
def FibreOrbit : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Std k r z z' → ∀ g₁ ∈ B.GV k r, ∀ g₂ ∈ B.GV k r,
    0 < Gf k r z z' g₁ → Zhat k r z z' g₁ = Zhat k r z z' g₂ →
      ∃ s ∈ CurvatureSupportSet k r z, ∃ s' ∈ CurvatureSupportSet k r z', g₂ = s⁻¹ * g₁ * s'
def FibreOrbitOfParts : Prop := WittExt → FixFrame → GramBlocks → GramIndependentSignature → FibreOrbit
def FibreStab : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), Std k r z z' → ∀ g ∈ B.GV k r, 0 < Gf k r z z' g →
    {p : B.Mat k r × B.Mat k r | p.1 ∈ CurvatureSupportSet k r z ∧ p.2 ∈ CurvatureSupportSet k r z' ∧ p.1⁻¹ * g * p.2 = g} =
      (fun h => (h, g⁻¹ * h * g)) '' KU k r z z' g
def Ml (k r l : ℕ) : ℕ := 2 * (r + 1 - l) + k + 1
def GramProductIdentity : Prop :=
  ∀ (k r : ℕ) (x : Fin (r + 1) → ℝ) (Gv : ℝ), 1 ≤ k → x 0 = 1 → (∀ l, 0 < x l) → 0 < Gv →
    (∏ l : Fin r, (x l.succ / x l.castSucc) ^ (2 * (Ml k r (l.val + 1) - 2))) * (Gv / x (Fin.last r) ^ 2) ^ (k - 1) =
      Gv ^ (k - 1) * ∏ l : Fin r, x l.succ ^ 4
def RootCOV : Prop :=
  ∀ (s : ℕ) (φ : ℂ → ℝ≥0∞), 1 ≤ s → Measurable φ →
    (∫⁻ D : ℂ, ((Polynomial.nthRoots s D).map φ).sum) =
      ∫⁻ z : ℂ, ENNReal.ofReal (((s : ℝ) ^ 2) * ‖z‖ ^ (2 * (s - 1))) * φ z
def LinCOV : Prop :=
  ∀ (a : ℂ) (φ : ℂ → ℝ≥0∞), a ≠ 0 → (∫⁻ c : ℂ, φ (a * c)) = ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) * ∫⁻ D : ℂ, φ D
def SliceDensityIndependent : Prop :=
  ∀ (s M : ℕ) (t : ℂ) (φ : ℂ → ℝ≥0∞), 1 ≤ s → 2 ≤ M → t ≠ 0 → Measurable φ →
    (∫⁻ c : ℂ, ENNReal.ofReal (‖t‖ ^ (2 * (s - 1) * (M + s - 2)) * ‖c‖ ^ (2 * (M - 2)) *
        (‖t‖ ^ (2 * (s - 1) ^ 2))⁻¹ * ((s : ℝ) ^ 2)⁻¹) *
      ((Polynomial.nthRoots s (c * t ^ (s - 1))).map fun z => ENNReal.ofReal (‖z‖ ^ (2 * (s - 1) ^ 2)) * φ z).sum) =
    ∫⁻ z : ℂ, ENNReal.ofReal (‖z‖ ^ (2 * s * (M + s - 3))) * φ z
def SliceDensityOfChangeOfVariables : Prop := RootCOV → LinCOV → SliceDensityIndependent
def SliceExponentIdentity : Prop := ∀ s M : ℤ, 2 * s * (M - 2) + 2 * (s - 1) ^ 2 + 2 * (s - 1) = 2 * s * (M + s - 3)
def StabBlock : Prop :=
  ∀ (p s : ℕ) (h lh uh : Matrix (Fin p) (Fin p) ℂ) (gs ls us : Matrix (Fin s) (Fin s) ℂ)
    (a : Matrix (Fin s) (Fin p) ℂ) (b : Matrix (Fin p) (Fin s) ℂ), IsUnit h.det → IsUnit gs.det →
    (Matrix.fromBlocks 1 0 a 1 * Matrix.fromBlocks lh 0 0 ls * Matrix.fromBlocks h 0 0 gs *
        (Matrix.fromBlocks uh 0 0 us * Matrix.fromBlocks 1 b 0 1) = Matrix.fromBlocks h 0 0 gs ↔
      (a = 0 ∧ b = 0 ∧ lh * h * uh = h ∧ ls * gs * us = gs))
def StabAntidiagExact : Prop :=
  ∀ (s : ℕ) (l u : Matrix (Fin s) (Fin s) ℂ) (t : ℂ), u ∈ UTset s → t ≠ 0 →
    (l * (t • antiW s) * u = t • antiW s ↔ l = antiW s * u⁻¹ * antiW s)
end Formalism.FourierDecayAlt.C2


