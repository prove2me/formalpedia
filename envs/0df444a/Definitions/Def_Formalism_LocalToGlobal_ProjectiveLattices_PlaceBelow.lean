-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:00.653388+00:00
-- url     : https://prove2.me/theorems/c38c8be8-a1e2-4205-ab0c-97b4518e4736
-- title:
--   Place Below
-- statement:
--   Definitions and structural lemmas for Place Below, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PlaceBelow.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
section Copies
variable {R : Type} [CommRing R] {d : ℕ}
def DofN (F : Fin d → PS R 2 d) {n : ℕ} (b : Fin n) (u : Fin d → R) (f : PS R n d) : PS R n d :=
  ∑ j : Fin d, (∑ i : Fin d, C (u i) * ev (n := n) ![pt R d b, 0] (pderiv R ((1 : Fin 2), i) (F j))) *
    pderiv R (b, j) f
def DmonN (F : Fin d → PS R 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → R)
    (m : ι →₀ ℕ) (f : PS R n d) : PS R n d :=
  (Finset.univ : Finset ι).toList.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f
def DpolyN (F : Fin d → PS R 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f : PS R n d) : PS R n d :=
  ∑ m ∈ P.support, C (P.coeff m) * DmonN F cp u m f
def nabValN {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (h : PS k 2 d) (w0 : O) (m : ℕ) {n : ℕ} (f : PS k n d) {ι : Type} [Fintype ι]
    (cp : ι → Fin n) (u : ι → Fin d → k) (P : MvPolynomial ι k) : k :=
  constantCoeff (DpolyN (B.FK k) cp u P
    (f * FB.expS k ((m : k) • ∑ b : Fin n, ev (n := n) ![pt k d b] (B.hL k h w0))))
end Copies
section Loc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable [StarRing (𝓞 E)]
abbrev IntChart (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) := IntegralChartA3 Xo c T io y
def FFV (T : CDVR) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (MvPolynomial (LtN Dw n) T.Fr) :=
  HaO Dw.mult n T.Fr (algebraMap T.V T.Fr).range ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)
def nuLocC {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntChart T io y) (e k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  letI := io.toAlgebra
  ⨅ (P : MvPolynomial (LtN Dw n) T.Fr) (_ : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n C.ch.d) (_ : IsIntPS T f),
    letI := io.toAlgebra
    nval T.V e (nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P)
def nuLoc {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    EReal :=
  ⨅ C : IntChart T io y, nuLocC C e k a n
variable (Xo c)
def nuSup (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  ⨆ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (y : IntFr Xo c T io) (_ : y.IsAlg),
    nuLoc y e k a n
def nuW (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : EReal :=
  max 0 (nuSup Xo c la k a n)
end Loc
section Num
structure DepPage where
  T : ℕ
  g1 : ℕ
  g2 : ℕ
  q1 : ℕ
  dd : ℕ
  sm : Finset ℕ
  f : ℕ
  r : ℕ
  vd : ℕ → ℝ
namespace DepPage
variable (Q : DepPage)
def n' : ℕ := 8 * Q.f * Q.r + 4
def q : ℕ := Q.g1 * Q.g2
def IsRam (p : ℕ) : Prop := p ∈ Q.sm ∨ p = Q.q1 ∨ p = Q.dd
def IsBad (p : ℕ) : Prop := Q.IsRam p ∨ p = Q.g1 ∨ p = Q.g2
open Classical in

def cP (DF : ℕ) (p : ℕ) : ℕ := if Q.IsRam p then ⌈Q.vd p * (DF : ℝ)⌉.toNat else 0
open Classical in

def nuN (DFL : ℕ) (nu : ℝ) (p : ℕ) : ℝ :=
  if p = Q.g1 then (DFL : ℝ) / ((Q.g1 : ℝ) - 1)
  else if p = Q.g2 then (DFL : ℝ) / ((Q.g2 : ℝ) - 1)
  else nu + (Q.cP DFL p : ℝ)
open Classical in

def eLam (eL : ℕ) (nuStar : ℝ) (p : ℕ) : ℕ :=
  ⌈(eL : ℝ) * (Q.T : ℝ) * (nuStar + if Q.IsBad p then 1 else 0)⌉.toNat
def Z1 (DFL DFF : ℕ) : ℕ :=
  (∏ p ∈ Q.sm.filter Nat.Prime, p ^ (Q.T * Q.cP DFL p + Q.cP DFF p)) * Q.q1 ^ (Q.T * Q.cP DFL Q.q1 + Q.cP DFF Q.q1) *
    Q.dd ^ (Q.T * Q.cP DFL Q.dd + Q.cP DFF Q.dd)
end DepPage
def nnOf {K : Type} [CommRing K] (pi pibar : Fin 2 → K) (Dp Dm : ℕ) : K :=
  ∏ i : Fin 2, pibar i ^ Dp * pi i ^ Dm
def sigOf {K : Type} [CommRing K] (Q : DepPage) (pi pibar : Fin 2 → K) (Dp Dm DFL DFF : ℕ) : K :=
  nnOf pi pibar Dp Dm * ((Q.q : K) ^ (Q.f * Q.r * Q.n') * (Q.Z1 DFL DFF : K))
end Num
section Places
def resCharOf {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  ringChar (𝓞 K ⧸ la.asIdeal)
def ramOverZ {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Ideal.ramificationIdx' (Ideal.span {((resCharOf la : ℕ) : ℤ)}) la.asIdeal
variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]
  [Algebra (𝓞 K) (𝓞 L)] [Algebra.IsIntegral (𝓞 K) (𝓞 L)]
def placeBelow (v : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := v.asIdeal.under (𝓞 K)
  isPrime := inferInstance
  ne_bot := Ideal.under_ne_bot (𝓞 K) v.ne_bot
def ramOver (v : HeightOneSpectrum (𝓞 L)) : ℕ :=
  Ideal.ramificationIdx' (placeBelow (K := K) v).asIdeal v.asIdeal
def expE (Q : DepPage) (nuStar : HeightOneSpectrum (𝓞 K) → ℝ) (v : HeightOneSpectrum (𝓞 L)) : ℕ :=
  ramOver (K := K) v * Q.eLam (ramOverZ (placeBelow (K := K) v)) (nuStar (placeBelow v))
    (resCharOf (placeBelow (K := K) v))
end Places
section Inst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
structure DepData (E : Type) [Field E] [NumberField E] where
  Q : DepPage
  aL : ℕ → (E →+* ℂ) × ℕ → ℕ
  aF : ℕ → (E →+* ℂ) × ℕ → ℕ
  nW : ℕ → ℕ
  Dp : ℕ → ℕ
  Dm : ℕ → ℕ
  pi : Fin 2 → 𝓞 E
variable {Xo c}
def nuWAt (D : DepData E) (la : HeightOneSpectrum (𝓞 c.F)) (j : ℕ) : EReal :=
  nuW Xo c la l.M (D.aL j) (D.nW j)
def nuStarAt (D : DepData E) (la : HeightOneSpectrum (𝓞 c.F)) (j : ℕ) : ℝ :=
  D.Q.nuN (DF Dw (D.aL j)) ((nuWAt (Xo := Xo) D la j).toReal / (ramOverZ la : ℝ)) (resCharOf la)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra (𝓞 c.F) (𝓞 LL)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 LL)]
def EAt (D : DepData E) (v : HeightOneSpectrum (𝓞 LL)) (j : ℕ) : ℕ :=
  expE (K := c.F) D.Q (fun la => nuStarAt (Xo := Xo) D la j) v
variable [Algebra (𝓞 E) LL]
def nnKAt (D : DepData E) (j : ℕ) : LL :=
  nnOf (fun i => algebraMap (𝓞 E) LL (D.pi i)) (fun i => algebraMap (𝓞 E) LL (H.bar (D.pi i))) (D.Dp j) (D.Dm j)
def sigAt (D : DepData E) (j : ℕ) : LL :=
  sigOf D.Q (fun i => algebraMap (𝓞 E) LL (D.pi i)) (fun i => algebraMap (𝓞 E) LL (H.bar (D.pi i))) (D.Dp j) (D.Dm j)
    (DF Dw (D.aL j)) (DF Dw (D.aF j))
end Inst
section Props
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
def IntChartEx : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → Nonempty (IntChart T io y)
def ChartIndep : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C C' : IntChart T io y) (e k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n = nuLocC C' e k a n
variable {Xo c}
def PiSplit (D : DepData E) : Prop :=
  D.pi 0 * H.bar (D.pi 0) = (D.Q.g1 : 𝓞 E) ∧ D.pi 1 * H.bar (D.pi 1) = (D.Q.g2 : 𝓞 E)
def LevelQ (D : DepData E) : Prop := (l.M : ℕ) = D.Q.g1 * D.Q.g2
def TPos (D : DepData E) : Prop := 1 ≤ D.Q.T
end Props
end Formalism.L2.Pj


