-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_GoodCount
-- name    : Formalism_MahlerMeasure_GoodCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:11.671604+00:00
-- url     : https://prove2.me/theorems/5920b796-f7e8-4bbe-87af-175c6c0781fe
-- title:
--   Good Count
-- statement:
--   Definitions and structural lemmas for Good Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/GoodCount.lean

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M
open MvPolynomial Finset
structure Letters (N : ℕ) where
  vec : Fin N → Bool
  deg : Fin N → ℕ
def MultiDeg {N r : ℕ} (LL : Letters N) (m : Fin N × Fin r →₀ ℕ) : Prop :=
  ∀ i, ∑ c, m (i, c) = LL.deg i
noncomputable def Pol (p : ℕ) [Fact p.Prime] (r : ℕ) {N : ℕ} (LL : Letters N) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p] {m | MultiDeg LL m}
noncomputable def IntPol (p : ℕ) [Fact p.Prime] (σ : Type) :
    Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]) :=
  LinearMap.range (MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p]) :
    MvPolynomial σ ℤ_[p] →ₐ[ℤ_[p]] MvPolynomial σ ℚ_[p]).toLinearMap
noncomputable def PolZ (p : ℕ) [Fact p.Prime] (r : ℕ) {N : ℕ} (LL : Letters N) :
    Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  (Pol p r LL).restrictScalars ℤ_[p] ⊓ IntPol p (Fin N × Fin r)
noncomputable def glAct (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ∑ i : Fin N,
    if (i : ℕ) < j then
      (if LL.vec i then (LinearMap.mulLeft ℚ_[p] (X (i, c))) ∘ₗ (pderiv (i, d)).toLinearMap
       else -((LinearMap.mulLeft ℚ_[p] (X (i, d))) ∘ₗ (pderiv (i, c)).toLinearMap))
    else 0
def wt {N r : ℕ} (LL : Letters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) : ℤ :=
  ∑ i : Fin N, if (i : ℕ) < j then (if LL.vec i then (m (i, c) : ℤ) else -(m (i, c) : ℤ)) else 0
def GlStable (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Prop :=
  ∀ c d, ∀ x ∈ S, glAct p LL j c d x ∈ S
noncomputable def gSpan (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sInf {S | F ∈ S ∧ GlStable p LL j S}
def FirstLE (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop :=
  ∀ G ∈ gSpan p LL j F, ∀ m ∈ G.support, ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M
noncomputable def YCond (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sSup {S | S ≤ MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M} ∧
    GlStable p LL j S}
noncomputable def Y (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Pol p r LL ⊓ ⨅ k, YCond p LL (J k) (M k)
noncomputable def YZ (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  (Y p LL J M).restrictScalars ℤ_[p] ⊓ PolZ p r LL
noncomputable def fock (p : ℕ) [Fact p.Prime] {σ : Type} (F G : MvPolynomial σ ℚ_[p]) : ℚ_[p] :=
  ∑ m ∈ F.support, F.coeff m * G.coeff m * (m.prod fun _ k => (k.factorial : ℚ_[p]))
noncomputable def fockN (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N)
    (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]) : ℚ_[p] :=
  fock p F G / ∏ i, ((LL.deg i).factorial : ℚ_[p])
noncomputable def tiePhiAt (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (a : Fin N) (b : Fin N) (z : ℕ) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  Formalism.GM.tiePhi (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (LL.deg a) (LL.deg b) z
structure TieData where
  t : ℕ
  pos : Fin t → ℕ
  z : Fin t → ℕ
  q : ℕ
  J : Fin q → ℕ
  thr : Fin q → WithTop ℤ
def TieData.Admissible {N : ℕ} (LL : Letters N) (T : TieData) : Prop :=
  StrictMono T.pos ∧
  (∀ i, ∃ h : T.pos i + 1 < N, LL.vec ⟨T.pos i, by omega⟩ = true ∧ LL.vec ⟨T.pos i + 1, h⟩ = false) ∧
  (∀ i, ∃ k, T.J k = T.pos i + 1)
noncomputable def TieData.phi (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (T : TieData) (i : Fin T.t) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  if h : T.pos i + 1 < N then tiePhiAt p LL ⟨T.pos i, by omega⟩ ⟨T.pos i + 1, h⟩ (T.z i) else LinearMap.id
def TieData.S {N : ℕ} (LL : Letters N) (T : TieData) (i : Fin T.t) : ℕ :=
  ∑ a : Fin N, if (a : ℕ) ≤ T.pos i then LL.deg a else 0
noncomputable def goodCount (p : ℕ) [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℤ_[p] Vs]
    (be : Vs → Vs → ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ) : ℕ :=
  sSup {n | ∃ x y : Fin n → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
    ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0}
noncomputable def bad (p : ℕ) [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℤ_[p] Vs]
    (be : Vs → Vs → ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ) : ℕ :=
  Module.finrank ℤ_[p] L - goodCount p be L D
noncomputable def lg (p : ℕ) (nmax r : ℕ) : ℝ := Real.logb p (4 * nmax + r) + 1
end Formalism.GM.M


