-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_SSmall
-- name    : Formalism_SizeWindowBrackets_SSmall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:39.549027+00:00
-- url     : https://prove2.me/theorems/4895d1f8-f8ed-4b5d-8e8b-21d1c1f0e27d
-- title:
--   SSmall
-- statement:
--   Definitions and structural lemmas for SSmall, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/SSmall.lean

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.LFunctionChainParameters.LSmall
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
def Delta2EvPow : Prop :=
  ∀ C C₂ C₃ A ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ n Lw δ₂ : ℝ,
    1 ≤ n → Real.log n ≤ C₂ * Real.log x → 2 ≤ Lw → Lw ≤ C₃ * Real.log x ^ A →
    Real.exp (-(C * Real.sqrt (Real.log n * Real.log Lw))) / Lw ≤ δ₂ → x ^ (-ε) ≤ δ₂
def Delta2Ev : Prop :=
  ∀ C C₂ C₃ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ n Lw δ₂ : ℝ,
    1 ≤ n → Real.log n ≤ C₂ * Real.log x → 2 ≤ Lw → Lw ≤ C₃ * Real.log x →
    Real.exp (-(C * Real.sqrt (Real.log n * Real.log Lw))) / Lw ≤ δ₂ → x ^ (-ε) ≤ δ₂
def Delta2Set : Prop :=
  ∀ C C₂ C₃ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (T2 : Finset H) (Lw : ℕ),
    Real.log (Fintype.card H) ≤ C₂ * Real.log x → 2 ≤ Lw → (Lw : ℝ) ≤ C₃ * Real.log x →
    (Fintype.card H : ℝ) * Real.exp (-(C * Real.sqrt (Real.log (Fintype.card H) * Real.log Lw))) / Lw ≤ (T2.card : ℝ) →
    x ^ (-ε) ≤ delta2 T2
def Delta2NeedsLw : Prop :=
  ∀ c ε x : ℝ, 0 < ε → ε < c → 1 < x → 2 ≤ x ^ c →
    ∃ n Lw δ₂ : ℝ, 1 ≤ n ∧ Real.log n ≤ 1 * Real.log x ∧ 2 ≤ Lw ∧ Lw ≤ x ^ c ∧
      Real.exp (-(0 * Real.sqrt (Real.log n * Real.log Lw))) / Lw ≤ δ₂ ∧ δ₂ < x ^ (-ε)
def Delta2Sat : Prop :=
  ∀ C C₂ C₃ : ℝ, 0 ≤ C → 0 ≤ C₂ → 0 < C₃ → ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x →
    1 ≤ x ^ C₂ ∧ Real.log (x ^ C₂) ≤ C₂ * Real.log x ∧ 2 ≤ C₃ * Real.log x ∧
    Real.exp (-(C * Real.sqrt (Real.log (x ^ C₂) * Real.log (C₃ * Real.log x)))) / (C₃ * Real.log x) ≤ 1 / 2
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def NodeWindows {m : ℕ} (TT T2 : Finset H) (b η w'' off : ℝ) (bt : H → ℝ) (w : H → Fin m → E0 × H → ℝ) : Prop :=
  (∀ u0 j ρ, IsThickAt T2 u0 ρ → b ≤ w u0 j ρ ∧ w u0 j ρ ≤ b + (η + 1)) ∧
  (∀ u0 j t, t ∈ TT → bt t + off ≤ w u0 j (topPl t) ∧ w u0 j (topPl t) ≤ bt t + off + η) ∧
  (∀ u0 j ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → (∀ t ∈ TT, ρ ≠ topPl t) → w'' ≤ w u0 j ρ ∧ w u0 j ρ ≤ w'' + η)
def WindowSizes (TT : Finset H) (x b b' η κ w'' off : ℝ) (bt : H → ℝ) : Prop :=
  0 < b ∧ 0 < b' ∧ 0 ≤ η ∧ 0 ≤ κ ∧ 0 < x ∧ 0 ≤ off ∧ off ≤ b' / x ∧ 0 < w'' ∧ w'' ≤ b' / x ∧
  (∀ t ∈ TT, b' ≤ bt t ∧ bt t ≤ b' + κ * b') ∧ κ * b' + b' / x + η ≤ b'
def NodeSizesOfWindows : Prop :=
  ∀ {m : ℕ} (TT T2 : Finset H) (x b b' η κ w'' off : ℝ) (bt : H → ℝ) (w : H → Fin m → E0 × H → ℝ),
    WindowSizes TT x b b' η κ w'' off bt → NodeWindows TT T2 b η w'' off bt w → NodeSizes T2 b b' η w
def WindowSizesText : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (TT : Finset H) (x b b' η κ off : ℝ) (bt : H → ℝ),
    3 ≤ x → 0 < b → 0 < b' → 0 ≤ η → η ≤ b' / 4 → 0 ≤ κ → κ ≤ 1 / 4 →
    (off = b' / x ∨ off = (⌊b' / x⌋ : ℝ)) → (∀ t ∈ TT, b' ≤ bt t ∧ bt t ≤ b' + κ * b') →
    WindowSizes TT x b b' η κ (b' / (x * (Fintype.card H : ℝ))) off bt
def NodeSizesText : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (m : ℕ) (TT T2 : Finset H) (x b b' η κ off : ℝ) (bt : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ),
    3 ≤ x → 0 < b → 0 < b' → 0 ≤ η → η ≤ b' / 4 → 0 ≤ κ → κ ≤ 1 / 4 →
    (off = b' / x ∨ off = (⌊b' / x⌋ : ℝ)) → (∀ t ∈ TT, b' ≤ bt t ∧ bt t ≤ b' + κ * b') →
    NodeWindows TT T2 b η (b' / (x * (Fintype.card H : ℝ))) off bt w → NodeSizes T2 b b' η w
def NodeWindowsExist : Prop :=
  ∀ (m : ℕ) (TT T2 : Finset H) (b η w'' off : ℝ) (bt : H → ℝ), 0 ≤ η →
    ∃ w : H → Fin m → E0 × H → ℝ, NodeWindows TT T2 b η w'' off bt w
def LiesOverFirstEmbedding (ρ : E0 × H) : Prop := ρ.1 = (0, 0)
def LiesOverSecondEmbedding (ρ : E0 × H) : Prop := ρ.1 = (0, 1)
def PlacesSplit : Prop :=
  ∀ ρ : E0 × H, (InPhi ρ ↔ LiesOverFirstEmbedding ρ ∨ LiesOverSecondEmbedding ρ) ∧ ¬ (LiesOverFirstEmbedding ρ ∧ LiesOverSecondEmbedding ρ)
def PartnerClasses : Prop :=
  ∀ t h : H,
    partner t (((1, 1), h) : E0 × H) = topPl (t + h) ∧
    partner t (((1, 0), h) : E0 × H) = thickPl (t + h) ∧
    cconj + (((1, 1), h) : E0 × H) + thickPl t = thickPl (t + h) ∧
    cconj + (((1, 0), h) : E0 × H) + thickPl t = topPl (t + h)
def ThickPlacesOverSecondEmbedding : Prop :=
  (∀ t : H, LiesOverFirstEmbedding (topPl t)) ∧ ∀ (T2 : Finset H) (u0 : H) (ρ : E0 × H), IsThickAt T2 u0 ρ → LiesOverSecondEmbedding ρ
def OrbitOfBaseClass : Prop :=
  ∀ (t h : H) (i : ℕ),
    (InPhi (i • (((1, 1), h) : E0 × H)) ↔ Even i) ∧
    (Even i → i • (((1, 1), h) : E0 × H) + topPl t = topPl (t + i • h)) ∧
    (Odd i → partner t (i • (((1, 1), h) : E0 × H)) = topPl (t + i • h))
def OrbitOfSigmaBaseClass : Prop :=
  ∀ (t h : H) (i : ℕ),
    (InPhi (i • (((1, 0), h) : E0 × H)) ↔ Even i) ∧
    (Even i → i • (((1, 0), h) : E0 × H) + topPl t = topPl (t + i • h)) ∧
    (Odd i → partner t (i • (((1, 0), h) : E0 × H)) = thickPl (t + i • h))
def BaseClassPartnerNeverThick : Prop :=
  ∀ (φ : E0 × H) (t : H) (i : ℕ) (T2 : Finset H) (u0 : H), φ.1 = (1, 1) → ¬ InPhi (i • φ) →
    LiesOverFirstEmbedding (partner t (i • φ)) ∧ ¬ IsThickAt T2 u0 (partner t (i • φ))
def GainDependsOverFirstEmbedding : Prop :=
  ∀ (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (p : ℕ) (w w' : E0 × H → ℝ),
    (D.frob p).1 = (1, 1) → (∀ ρ, LiesOverFirstEmbedding ρ → w ρ = w' ρ) → askP D N a t w p = askP D N a t w' p
def AskFreeTranslate : Prop :=
  ∀ (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (p : ℕ) (T2 : Finset H) (w : H → E0 × H → ℝ),
    (D.frob p).1 = (1, 1) →
    (∀ u0 u0' ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → ¬ IsThickAt T2 u0' ρ → w u0 ρ = w u0' ρ) →
    ∀ u0 u0', askP D N a t (w u0) p = askP D N a t (w u0') p
end
def AskSignalDepends : Prop :=
  ∃ (D : ArithData (ZMod 2)) (N : ℕ) (a : ℝ) (t : ZMod 2) (p : ℕ) (T2 : Finset (ZMod 2)) (w : ZMod 2 → E0 × ZMod 2 → ℝ),
    (D.frob p).1 = (1, 0) ∧
    (∀ u0 u0' ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → ¬ IsThickAt T2 u0' ρ → w u0 ρ = w u0' ρ) ∧
    ∃ u0 u0', askP D N a t (w u0) p ≠ askP D N a t (w u0') p
section Conj
open Matrix Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
def cj {m n : Type} (M : Matrix m n ℂ) : Matrix m n ℂ := M.map (starRingEnd ℂ)
def Bconj {ι : Type} {D : ℕ} {d : ι → ℕ} (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) :
    ∀ u, Matrix (Fin D) (Fin (d u)) ℂ := fun u => cj (B u)
def ConjHs : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] (M : Matrix m n ℂ), hsSq (cj M) = hsSq M ∧ hsNorm (cj M) = hsNorm M
def ConjAlg : Prop :=
  ∀ (l m n : Type) [Fintype l] [Fintype m] [Fintype n] [DecidableEq m] (M : Matrix l m ℂ) (M' : Matrix m n ℂ)
    (P : Matrix l n ℂ) (K : Matrix m m ℂ),
    cj (cj M) = M ∧ cj (M * M') = cj M * cj M' ∧ cj Mᴴ = (cj M)ᴴ ∧ cj (1 : Matrix m m ℂ) = 1 ∧
    (cj K).trace = starRingEnd ℂ K.trace ∧ ((cj M)ᴴ * cj P = 0 ↔ Mᴴ * P = 0)
def ConjKQ : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ),
    (∀ u u', Kp (Bconj B) ga u u' = cj (Kp B ga u u')) ∧
    (∀ u, Kd (Bconj B) ga u - 1 = cj (Kd B ga u - 1)) ∧
    Qm (Bconj B) ga = cj (Qm B ga)
def ConjTraces : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ),
    (∀ u u', hsSq (Kp (Bconj B) ga u u') = hsSq (Kp B ga u u')) ∧
    (∀ u, hsSq (Kd (Bconj B) ga u - 1) = hsSq (Kd B ga u - 1)) ∧
    (Qm (Bconj B) ga).trace.re = (Qm B ga).trace.re ∧
    (Qm (Bconj B) ga * Qm (Bconj B) ga).trace.re = (Qm B ga * Qm B ga).trace.re
def ConjInv : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ),
    (∀ η, F1 (Bconj B) ga η ↔ F1 B ga η) ∧
    (∀ e, F2 (Bconj B) ga e ↔ F2 B ga e) ∧
    (∀ Dstar η0 η1 e0, InputS (Bconj B) ga Dstar η0 η1 e0 ↔ InputS B ga Dstar η0 η1 e0)
def ConjRam : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ),
    (Isom (fun u => cj (V u)) ↔ Isom V) ∧ Bram (Bconj B) (fun u => cj (V u)) = Bconj (Bram B V)
def ConjRange : Prop :=
  ∀ (n D : ℕ) (A : Matrix (Fin D) (Fin n) ℂ) (y : Fin D → ℂ),
    (y ∈ Set.range (cj A).mulVec ↔ star y ∈ Set.range A.mulVec)
def ConjSemilinear : Prop :=
  ∀ (n D : ℕ) (T : (Fin n → ℂ) →ₛₗ[starRingEnd ℂ] (Fin D → ℂ)),
    ∃! A : Matrix (Fin D) (Fin n) ℂ, (∀ x, T x = A.mulVec (star x)) ∧ ∀ x, star (T x) = (cj A).mulVec x
end Conj
section Host
open Formalism.LFunctionChainParameters.LHost
def hOf (e m : ℕ) : HA e :=
  if h : m.Coprime (2 ^ (e + 2)) then Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitOfCoprime m h)) else 0
def ArtNegOne : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
    Multiplicative.toAdd (recMap e q d (-1)) = cconj
def ArtFormula : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ u : (ZMod (hostN e q d))ˣ,
    (chC : AddChar (E0 × HA e) ℂ) (Multiplicative.toAdd (recMap e q d u))
      = ((jacobiSym ((u : ZMod (hostN e q d)).val : ℤ) d : ℤ) : ℂ) ∧
    (psC : AddChar (E0 × HA e) ℂ) (Multiplicative.toAdd (recMap e q d u))
      = ((jacobiSym ((u : ZMod (hostN e q d)).val : ℤ) q : ℤ) : ℂ) ∧
    (Multiplicative.toAdd (recMap e q d u)).2 = hOf e (u : ZMod (hostN e q d)).val
def decomp {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (p : ℕ) : AddSubgroup (E0 × H) :=
  D.inertia p ⊔ AddSubgroup.zmultiples (D.frob p)
def DecompHost : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
    (∀ x, x ∈ decomp (hostData e q d) 2 ↔ InPhi x) ∧
    (∀ x, x ∈ decomp (hostData e q d) q ↔ InPhi x ∧ x.2 ∈ AddSubgroup.zmultiples (hOf e q)) ∧
    (∀ x, x ∈ decomp (hostData e q d) d ↔ ∃ i : ℤ, x.2 = i • hOf e d ∧ x.1.2 = (i : ZMod 2))
def CconjNotDecomp : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → 2 ≤ e →
    cconj ∉ decomp (hostData e q d) 2 ∧ cconj ∉ decomp (hostData e q d) q ∧ cconj ∉ decomp (hostData e q d) d
def CconjDecompSmall : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → e ≤ 1 → cconj ∈ decomp (hostData e q d) d
def Sloc {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (g : E0 × H) (n : ℕ) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * primVal D ψ n
def LemmaC : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ (g : E0 × HA e) (i : ℕ), 1 ≤ i →
    Sloc (hostData e q d) g (2 ^ i)
      = (1 / ((PhiSet (H := HA e)).card : ℂ)) * (1 + psC g * ((jacobiSym 2 q : ℤ) : ℂ) ^ i) * (1 + chC g) ∧
    Sloc (hostData e q d) g (q ^ i) = (1 / 2) * (if g.2 = i • hOf e q then 1 else 0) * (1 + chC g) ∧
    Sloc (hostData e q d) g (d ^ i) = (1 / 2) * (if g.2 = i • hOf e d then 1 else 0) * (1 + (-1) ^ i * psC g)
def gI (e d i : ℕ) : E0 × HA e := (if Odd i then (1, 1) else (1, 0), i • hOf e d)
def ParityRule : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ i : ℕ,
    (∀ g : E0 × HA e, (g - i • (hostData e q d).frob d ∈ (hostData e q d).inertia d ∧ ¬ InPhi g) ↔ g = gI e d i) ∧
    ∀ t : HA e, partner t (gI e d i) = if Odd i then topPl (t + i • hOf e d) else thickPl (t + i • hOf e d)
def OutsidePhi : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ (g : E0 × HA e) (i : ℕ), 1 ≤ i → ¬ InPhi g →
    Sloc (hostData e q d) g (2 ^ i) = 0 ∧ Sloc (hostData e q d) g (q ^ i) = 0 ∧
    Sloc (hostData e q d) g (d ^ i) = if g = gI e d i then 1 else 0
def AskDExplicit : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
  ∀ (N : ℕ) (a : ℝ) (t : HA e) (w : E0 × HA e → ℝ),
    askD (hostData e q d) N a t w = ∑ i ∈ Icc 1 N, max (a / (d : ℝ) ^ i - w (partner t (gI e d i))) 0
def CharSplit : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (ψ : AddChar (E0 × H) ℂ),
    (ψ sg = 1 ∨ ψ sg = -1) ∧ (ψ sgc0 = 1 ∨ ψ sgc0 = -1) ∧
    ∀ g : E0 × H, ψ g = ψ ((0, 0), g.2) * (if ψ sg = 1 then 1 else psC g) * (if ψ sgc0 = 1 then 1 else chC g)
def omV (e : ℕ) (ψ : AddChar (E0 × HA e) ℂ) (m : ℕ) : ℂ := by
  classical
  exact if ∀ t : HA e, ψ ((0, 0), t) = 1 then 1 else if Odd m then ψ ((0, 0), hOf e m) else 0
def laV (s : ℂ) (l m : ℕ) : ℂ := by
  classical
  exact if s = 1 then 1 else ((jacobiSym (m : ℤ) l : ℤ) : ℂ)
def ProductFormula : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ (ψ : AddChar (E0 × HA e) ℂ) (m : ℕ), m ≠ 0 →
    primVal (hostData e q d) ψ m = omV e ψ m * laV (ψ sg) q m * laV (ψ sgc0) d m
end Host
end Formalism.LFunctionChainParameters.LSmall


