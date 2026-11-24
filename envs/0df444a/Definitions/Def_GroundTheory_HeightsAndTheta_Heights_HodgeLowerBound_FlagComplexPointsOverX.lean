-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagComplexPointsOverX
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagComplexPointsOverX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:09:28.909922+00:00
-- url     : https://prove2.me/theorems/9908d20c-d93a-44e5-bcd8-2746beaf0256
-- title:
--   Flag Complex Points Over X
-- statement:
--   Definitions and structural lemmas for Flag Complex Points Over X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FlagComplexPointsOverX.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_TorusInvariantK0RegCusp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
open MvPolynomial Filter Topology Matrix ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
section Roots
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
abbrev Rts : Type := MvPolynomial (Ψ × Fin N) ℚ
variable {Ψ N}
def lin (la : Ψ × Fin N → ℤ) : Rts Ψ N := ∑ x, C (la x : ℚ) * X x
def la0 (j : ℕ) : Ψ × Fin N → ℤ := fun x => if (x.2 : ℕ) < j then 0 else -1
def muPoly (j : ℕ) : Rts Ψ N := lin (la0 j)
def altRho {R : Type} [CommRing R] (r : ℕ) (v : Fin r → R) : R :=
  (Matrix.of fun i l : Fin r => v i ^ (r - 1 - (l : ℕ))).det
def yv (j : ℕ) (hj : j ≤ N) (τ : Ψ) : Fin j → Rts Ψ N := fun i => X (τ, ⟨i, by omega⟩)
def zv (j : ℕ) (τ : Ψ) : Fin (N - j) → Rts Ψ N := fun l => X (τ, ⟨j + l, by omega⟩)
def fibV (j : ℕ) (hj : j ≤ N) : Rts Ψ N := ∏ τ, altRho j (yv j hj τ) * altRho (N - j) (zv j τ)
def cf (n : ℕ) : ℚ := (-1) ^ n
def fib (j : ℕ) (hj : j ≤ N) (n : ℕ) : Rts Ψ N := C (cf n) * fibV j hj
def FA (j : ℕ) (hj : j ≤ N) (n : ℕ) : Rts Ψ N := muPoly j ^ (n + 1) * fib j hj n
def antisym (G : Finset (Equiv.Perm (Ψ × Fin N))) (g : Rts Ψ N) : Rts Ψ N :=
  ∑ w ∈ G, ((Equiv.Perm.sign w : ℤ) : ℚ) • rename w g
def G0 (j : ℕ) : Finset (Equiv.Perm (Ψ × Fin N)) :=
  Finset.univ.filter fun w => ∀ x, (w x).1 = x.1 ∧ (((w x).2 : ℕ) < j ↔ (x.2 : ℕ) < j)
def Gfull : Finset (Equiv.Perm (Ψ × Fin N)) :=
  Finset.univ.filter fun w => ∀ x, (w x).1 = x.1
def delta0 (j : ℕ) : Ψ × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => if (x.2 : ℕ) < j then (x.2 : ℕ) else (x.2 : ℕ) - j
def deltaFull : Ψ × Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm fun x => (x.2 : ℕ)
def fdeg (j : ℕ) (hj : j ≤ N) : ℚ := coeff (delta0 j) (antisym (G0 j) (fibV (Ψ := Ψ) j hj))
def Jint (j : ℕ) (hj : j ≤ N) (n : ℕ) : ℚ :=
  coeff deltaFull (antisym Gfull (muPoly (Ψ := Ψ) (N := N) j ^ n * fib j hj n))
end Roots
section Polar
variable {σ : Type} [Fintype σ] [DecidableEq σ]
def polar (d : ℕ) (Pf : (σ → ℤ) → ℝ) (α : σ →₀ ℕ) : ℝ :=
  if (α.sum fun _ m => m) = d then
    (1 / (d.factorial : ℝ)) * ∑ β ∈ Finset.Iic α,
      (-1 : ℝ) ^ (d - β.sum fun _ m => m) * (∏ x, ((α x).choose (β x) : ℝ)) * Pf (fun x => (β x : ℤ))
  else 0
def PP (d : ℕ) (Pf : (σ → ℤ) → ℝ) (F : MvPolynomial σ ℚ) : ℝ :=
  ∑ α ∈ F.support, ((coeff α F : ℚ) : ℝ) * polar d Pf α
end Polar
section Y0
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace ComponentData
variable (D : ComponentData Ψ K ι)
def flagGenericMatrix (τ : Ψ) : Matrix (Fin D.N) (Fin D.N1) (MvPolynomial (Ψ × Fin D.N × Fin D.N) (FnField D.P)) :=
  Matrix.of fun a l =>
    if (a : ℕ) < D.N - D.j then
      ∑ b : Fin (D.N - D.j), X (τ, a, ⟨b, by have := b.2; omega⟩) * C (D.hodge τ b l)
    else ∑ b : Fin D.N, X (τ, a, b) * C (D.basis τ b l)
def flagGenericPointMap : MRing (FlagBundleBlocksOverX ι Ψ D.N1 D.N) →+* MvPolynomial (Ψ × Fin D.N × Fin D.N) (FnField D.P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt D.P ⟨k, i⟩)
    | ⟨.inr q, S⟩ => flagMinor (D.flagGenericMatrix q.1) q.2 S
def flagBundleIdeal : Ideal (MRing (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) := RingHom.ker D.flagGenericPointMap
def flagBundleDimension : ℕ := D.n + D.f * (D.j * (D.j - 1) / 2 + D.jp * (D.jp - 1) / 2)
def xPart (w : Cone (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) : Cone ι := fun p => w ⟨.inl p.1, p.2⟩
def flagComplexPointsOverX : Set (Cone (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) := {w | w ∈ mcPts D.flagBundleIdeal ∧ D.xPart w ∈ D.Xo}
def liftX (A : HermLine ι) : HermLine (FlagBundleBlocksOverX ι Ψ D.N1 D.N) where
  a := Sum.elim A.a 0
  h w := A.h (D.xPart w)
  pos w hw := A.pos _ fun k => hw (Sum.inl k)
  smul c w hc := by
    have e : D.xPart (fun p => c p.1 * w p) = fun p => (fun k => c (Sum.inl k)) p.1 * D.xPart w p := rfl
    rw [e, A.smul _ _ (fun k => hc _), Fintype.prod_sum_type]
    simp
def cCoef (la : Ψ × Fin D.N → ℤ) (τ : Ψ) (r : Fin D.N) : ℤ :=
  if h : (r : ℕ) + 1 < D.N then la (τ, ⟨D.N - r - 1, by omega⟩) - la (τ, ⟨D.N - r - 2, by omega⟩)
  else -la (τ, ⟨0, by have := r.2; omega⟩)
def lineDeg (τ : Ψ) (r : Fin D.N) : K ⊕ (Ψ × Fin (D.N - 1)) → ℤ :=
  if h : (r : ℕ) + 1 < D.N then
    Sum.elim (fun k => -(((r : ℤ) + 1) * D.twist τ k)) (fun q => if q = (τ, ⟨r, by omega⟩) then 1 else 0)
  else Sum.elim (D.detLine τ).a 0
def flagDegreeVector (la : Ψ × Fin D.N → ℤ) : K ⊕ (Ψ × Fin (D.N - 1)) → ℤ :=
  ∑ x : Ψ × Fin D.N, D.cCoef la x.1 x.2 • D.lineDeg x.1 x.2
def regWeight (la : Ψ × Fin D.N → ℤ) (t : ℝ) (w : Cone (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) : ℝ :=
  ∑ x : Ψ × Fin D.N, (D.cCoef la x.1 x.2 : ℝ) * D.regFl t x.1 x.2 w
omit [DecidableEq Ψ] in
theorem regWeight_inv (la : Ψ × Fin D.N → ℤ) (t : ℝ) : IsTorusInv (D.regWeight la t) := fun c w hc => by
  simp only [regWeight, D.regFl_inv _ _ _ c w hc]
def verticalLatticeBundle (B : ℕ) (la : Ψ × Fin D.N → ℤ) : HermLine ι :=
  tensorList ((D.SB B).toList.flatMap fun p =>
    (Finset.univ : Finset (Ψ × Fin D.N)).toList.map fun x => hzpow (D.latFl p x.1 x.2) (D.cCoef la x.1 x.2))
def LT (B : ℕ) (la : Ψ × Fin D.N → ℤ) (t : ℝ) : HermLine (FlagBundleBlocksOverX ι Ψ D.N1 D.N) :=
  (htwist (fsLine (D.flagDegreeVector la)) (D.regWeight la t) (D.regWeight_inv la t)).tensor (D.liftX (D.verticalLatticeBundle B la))
def PB (II : IntersectionSystem) (B : ℕ) (la : Ψ × Fin D.N → ℤ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun t =>
    II (K ⊕ (Ψ × Fin (D.N - 1))) (FlagBundleBlocksOverX ι Ψ D.N1 D.N) D.flagBundleIdeal (D.flagBundleDimension + 1) (fun _ => D.LT B la t)
omit [DecidableEq Ψ] in
theorem j_le_N : D.j ≤ D.N := D.j_lt_N.le
def FA' : Rts Ψ D.N := FA D.j D.j_le_N D.n
def PPB (II : IntersectionSystem) (B : ℕ) : ℝ := PP (D.flagBundleDimension + 1) (D.PB II B) D.FA'
def fdeg' : ℚ := fdeg (Ψ := Ψ) D.j D.j_le_N
def J' : ℚ := Jint (Ψ := Ψ) D.j D.j_le_N D.n
def plNormSq {N1 m : ℕ} (H : Matrix (Fin N1) (Fin N1) ℂ) (p : {S : Finset (Fin N1) // S.card = m} → ℂ) : ℝ :=
  (∑ S, ∑ S', star (p S) * (H.submatrix (S.1.orderEmbOfFin S.2) (S'.1.orderEmbOfFin S'.2)).det * p S').re
def hodgeLineW (τ : Ψ) (r : Fin D.N) (w : Cone (FlagBundleBlocksOverX ι Ψ D.N1 D.N)) : ℝ :=
  if h : (r : ℕ) + 1 < D.N then
    (1 / 2) * Real.log (plNormSq (D.metric τ (D.xPart w))
        (fun S : PluckerBlocks D.N1 D.N ⟨r, by omega⟩ => w ⟨Sum.inr (τ, ⟨r, by omega⟩), S⟩)) -
      Real.log ((fsLine (D.lineDeg τ r)).h w)
  else Real.log ((D.detLine τ).h (D.xPart w)) - Real.log ((fsLine (D.lineDeg τ r)).h w)
end ComponentData
end Y0
section FlZ
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
abbrev FlZBlk : Ψ × Fin (N - 1) → Type := fun q => PluckerBlocks N N q.2
def genT (τ : Ψ) : Matrix (Fin N) (Fin N) (MvPolynomial (Ψ × Fin N × Fin N) ℤ) := Matrix.of fun a b => X (τ, a, b)
def flZMap : MRing (FlZBlk Ψ N) →+* MvPolynomial (Ψ × Fin N × Fin N) ℤ :=
  eval₂Hom (Int.castRingHom _) fun q => flagMinor (genT Ψ N q.1.1) q.1.2 q.2
def FlZIdeal : Ideal (MRing (FlZBlk Ψ N)) := RingHom.ker (flZMap Ψ N)
def dimFl : ℕ := Fintype.card Ψ * (N * (N - 1) / 2)
variable {Ψ N}
def flDeg (la : Ψ × Fin N → ℤ) : Ψ × Fin (N - 1) → ℤ :=
  fun q => la (q.1, ⟨q.2 + 1, by omega⟩) - la (q.1, ⟨q.2, by omega⟩)
def PFl (II : IntersectionSystem) (la : Ψ × Fin N → ℤ) : ℝ :=
  II (Ψ × Fin (N - 1)) (FlZBlk Ψ N) (FlZIdeal Ψ N) (dimFl Ψ N + 1) (fun _ => fsLine (flDeg la))
def hFl (II : IntersectionSystem) (F : Rts Ψ N) : ℝ := PP (dimFl Ψ N + 1) (PFl II) F
end FlZ
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine


