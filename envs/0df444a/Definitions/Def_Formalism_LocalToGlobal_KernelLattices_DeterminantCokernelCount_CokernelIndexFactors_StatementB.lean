-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_KernelLattices_DeterminantCokernelCount_CokernelIndexFactors_StatementB
-- name    : Formalism_LocalToGlobal_KernelLattices_DeterminantCokernelCount_CokernelIndexFactors_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:26.459808+00:00
-- url     : https://prove2.me/theorems/1baa8550-3398-4159-9ec4-2deafcb3d725
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/KernelLattices/DeterminantCokernelCount/CokernelIndexFactors/StatementB.lean

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
open scoped ComplexOrder
namespace Formalism.L2.Ker.JMB
abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ
def rtd (d : ℕ) : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ)
def w0 (d : ℕ) : ℂ := (1 + rtd d) / 2
def OK (d : ℕ) : Set ℂ := {z | ∃ u v : ℤ, z = (u : ℂ) + (v : ℂ) * w0 d}
def eisOK (d k : ℕ) : ℂ := ∑' w : {w : ℂ // w ∈ OK d ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)
def discrOK (d : ℕ) : ℂ := (60 * eisOK d 2) ^ 3 - 27 * (140 * eisOK d 3) ^ 2
variable {g : ℕ}
def hf (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ :=
  ∑ i, ∑ j, z i * Hm i j * (starRingEnd ℂ) (w j)
def beta (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ :=
  ((Real.sqrt d / 2 : ℝ) : ℂ) * hf Hm z w
def opU (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) : (Fin g → ℂ) → ℂ :=
  fun z => F (z + x) * Complex.exp (-(Real.pi : ℂ) * hf Hm z x - (Real.pi : ℂ) / 2 * hf Hm x x)
def opW (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ) (F : (Fin g → ℂ) → ℂ) : (Fin g → ℂ) → ℂ :=
  fun z => Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta d Hm x x).re : ℂ)) * opU Hm x F z
def kap (Hm : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((hf Hm x y).im : ℂ))
structure Setup (g : ℕ) where
  d : ℕ
  Hm : Matrix (Fin g) (Fin g) ℂ
  La : Submodule ℤ (Fin g → ℂ)
def Setup.Ok (S : Setup g) : Prop :=
  S.d.Prime ∧ S.d % 16 = 7 ∧ S.Hm.PosDef ∧
  DiscreteTopology S.La ∧ Submodule.span ℝ (S.La : Set (Fin g → ℂ)) = ⊤ ∧
  (∀ x ∈ S.La, w0 S.d • x ∈ S.La) ∧
  (∀ x ∈ S.La, ∀ y ∈ S.La, beta S.d S.Hm x y ∈ OK S.d) ∧
  ∀ y : Fin g → ℂ, (∀ x ∈ S.La, ∃ k : ℤ, (hf S.Hm x y).im = k) → y ∈ S.La
def Setup.Rat (S : Setup g) (y : Fin g → ℂ) : Prop := ∃ s : ℕ, 0 < s ∧ (s : ℂ) • y ∈ S.La
def AlgDirL (La : Submodule ℤ (Fin g → ℂ)) (y : Fin g → ℂ) : Prop :=
  ∃ (s : ℕ) (c : Fin s → ℂ) (u : Fin s → Fin g → ℂ), (∀ k, c k ∈ Qbar) ∧ (∀ k, u k ∈ La) ∧ y = ∑ k, c k • u k
def Setup.AlgDir (S : Setup g) (y : Fin g → ℂ) : Prop := AlgDirL S.La y
def Setup.PrimeTo (S : Setup g) (q : ℕ) (t : Fin g → ℂ) : Prop :=
  ∃ s : ℕ, 0 < s ∧ Nat.Coprime s q ∧ (s : ℂ) • t ∈ S.La
def jetV (G : (Fin g → ℂ) → ℂ) {k : ℕ} (ys : Fin k → Fin g → ℂ) : ℂ :=
  iteratedFDeriv ℂ k G 0 ys
def Setup.IsTheta (S : Setup g) (e : (Fin g → ℂ) → ℂ) : Prop :=
  ContDiff ℂ ⊤ e ∧ ∀ x ∈ S.La, opW S.d S.Hm x e = e
def Setup.AlgJets (S : Setup g) (δ : ℂ) (e : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ), (∀ j, S.Rat (ys j)) → jetV e (fun j => δ⁻¹ • ys j) ∈ Qbar
variable {q : ℕ} [Fact q.Prime]
open Classical in

def lamA (lam : Qbar →+* ℂ_[q]) (x : ℂ) : ℂ_[q] :=
  if h : x ∈ Qbar then lam ⟨x, h⟩ else 0
def SplitK (d q : ℕ) : Prop :=
  (q = 2 ∧ d % 8 = 7) ∨ (q ≠ 2 ∧ jacobiSym (-(d : ℤ)) q = 1)
def Setup.NNBasis (S : Setup g) (q : ℕ) {r : ℕ} (b : Fin r → Fin g → ℂ) : Prop :=
  (∀ i, b i ∈ S.La) ∧
  (∀ y ∈ S.La, ∃ s : ℕ, Nat.Coprime s q ∧ ∃ c : Fin r → ℂ, (∀ i, c i ∈ OK S.d) ∧ (s : ℂ) • y = ∑ i, c i • b i) ∧
  ∀ c : Fin r → ℂ, (∀ i, c i ∈ OK S.d) → ∑ i, c i • b i = 0 → ∀ i, c i = 0
def IsIdem (lam : Qbar →+* ℂ_[q]) (d m : ℕ) (eps : ℂ) : Prop :=
  eps ∈ OK d ∧ ‖lamA lam eps - 1‖ ≤ (q : ℝ) ^ (-(m : ℤ)) ∧
    ‖lamA lam ((starRingEnd ℂ) eps)‖ ≤ (q : ℝ) ^ (-(m : ℤ))
def liftY (q n : ℕ) (eps : ℂ) {r : ℕ} (b : Fin r → Fin g → ℂ) (y : Fin r → Fin (q ^ n)) : Fin g → ℂ :=
  (eps / (q : ℂ) ^ n) • ∑ i, (((y i : ℕ) : ℂ)) • b i
def vecN {r : ℕ} (n : ℕ) (b : Fin r → Fin g → ℂ) (a : Fin r → Fin (q ^ n)) : Fin g → ℂ :=
  ∑ i, (((a i : ℕ) : ℂ)) • b i
def vecA {r : ℕ} (n : ℕ) (b : Fin r → Fin g → ℂ) (a : Fin r → ℤ_[q]) : Fin g → ℂ :=
  ∑ i, (((PadicInt.toZModPow n (a i)).val : ℕ) : ℂ) • b i
def zc (a : ℤ_[q]) : ℂ_[q] := algebraMap ℚ_[q] ℂ_[q] (a : ℚ_[q])
def pairD (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (b : Fin r → Fin g → ℂ)
    (y : Fin g → ℂ) (a : Fin r → ℤ_[q]) : ℂ_[q] :=
  Ω⁻¹ * ∑ i, zc (a i) * lamA lam (beta d Hm y (b i))
def FactorsMod {r : ℕ} (n : ℕ) (Φ : (Fin r → ℤ_[q]) → ℂ) : Prop :=
  ∀ a a' : Fin r → ℤ_[q], (∀ i, ‖a i - a' i‖ ≤ (q : ℝ) ^ (-(n : ℤ))) → Φ a = Φ a'
def xiF (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ) (eps : ℂ) {r : ℕ} (b : Fin r → Fin g → ℂ)
    (Φ : (Fin r → ℤ_[q]) → ℂ) (G : (Fin g → ℂ) → ℂ) : (Fin g → ℂ) → ℂ :=
  fun z => ((q : ℂ) ^ (n * r))⁻¹ * ∑ a : Fin r → Fin (q ^ n), Φ (fun i => (((a i : ℕ) : ℤ_[q]))) *
    ∑ y : Fin r → Fin (q ^ n), (kap Hm (vecN (q := q) n b a) (liftY q n eps b y))⁻¹ *
      opW d Hm (liftY q n eps b y) G z
def EqAtQ (q : ℕ) (La La' : Submodule ℤ (Fin g → ℂ)) : Prop :=
  ∃ s : ℕ, 0 < s ∧ Nat.Coprime s q ∧ (∀ x ∈ La, (s : ℂ) • x ∈ La') ∧ ∀ x ∈ La', (s : ℂ) • x ∈ La
def MomentProperty (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) (δ : ℂ) (S : Setup g) {r M : ℕ} (b : Fin r → Fin g → ℂ)
    (ts : Fin M → Fin g → ℂ) (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]) (G : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (n m : ℕ) (eps : ℂ), IsIdem lam S.d m eps → 2 * n ≤ m →
    (∀ (l : Fin M) (i : Fin r), ∃ z : ℤ, (hf S.Hm (eps • b i) (ts l)).im = z) →
    ∀ (y : Fin r → Fin (q ^ n)) (k : ℕ) (ys : Fin k → Fin g → ℂ), (∀ j, S.AlgDir (ys j)) →
    ∀ f : C(Fin r → ℤ_[q], ℂ_[q]),
      (∀ a, f a = lamA lam (kap S.Hm (vecA n b a) (liftY q n eps b y)) * ∏ j, pairD lam Ω S.d S.Hm b (ys j) a) →
      jetV (opW S.d S.Hm (liftY q n eps b y) G) (fun j => δ⁻¹ • ys j) ∈ Qbar ∧
        lamA lam (jetV (opW S.d S.Hm (liftY q n eps b y) G) (fun j => δ⁻¹ • ys j)) = μ f
def AveragedMomentProperty (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) (δ : ℂ) (S : Setup g) {r M : ℕ} (b : Fin r → Fin g → ℂ)
    (ts : Fin M → Fin g → ℂ) (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]) (G : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (n m : ℕ) (eps : ℂ), IsIdem lam S.d m eps → 2 * n ≤ m →
    (∀ (l : Fin M) (i : Fin r), ∃ z : ℤ, (hf S.Hm (eps • b i) (ts l)).im = z) →
    ∀ Φ : (Fin r → ℤ_[q]) → ℂ, FactorsMod n Φ → (∀ a, Φ a ∈ Qbar) →
    ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ), (∀ j, S.AlgDir (ys j)) →
    ∀ f : C(Fin r → ℤ_[q], ℂ_[q]),
      (∀ a, f a = lamA lam (Φ a) * ∏ j, pairD lam Ω S.d S.Hm b (ys j) a) →
      jetV (xiF S.d S.Hm n eps b Φ G) (fun j => δ⁻¹ • ys j) ∈ Qbar ∧
        lamA lam (jetV (xiF S.d S.Hm n eps b Φ G) (fun j => δ⁻¹ • ys j)) = μ f
def JetMomB : Prop :=
  ∀ (d q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (δ : ℂ), d.Prime → d % 16 = 7 → SplitK d q → δ ^ 12 = discrOK d →
  ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧
  ∀ (g : ℕ) (S : Setup g), S.d = d → S.Ok →
  ∀ (r : ℕ) (b : Fin r → Fin g → ℂ), S.NNBasis q b →
  ∀ e : (Fin g → ℂ) → ℂ, S.IsTheta e → S.AlgJets δ e →
  ∃ ν : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q],
    MomentProperty lam Ω δ S b (fun _ : Fin 0 => 0) ν e ∧ AveragedMomentProperty lam Ω δ S b (fun _ : Fin 0 => 0) ν e ∧
    ∀ t : Fin g → ℂ, S.PrimeTo q t →
    ∃ μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], ‖μ‖ = ‖ν‖ ∧
      MomentProperty lam Ω δ S b (fun _ : Fin 1 => t) μ (opU S.Hm t e) ∧
        AveragedMomentProperty lam Ω δ S b (fun _ : Fin 1 => t) μ (opU S.Hm t e)
def JetMomBC : Prop :=
  ∀ (d q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (δ : ℂ), d.Prime → d % 16 = 7 → SplitK d q → δ ^ 12 = discrOK d →
  ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧
  ∀ (g : ℕ) (S : Setup g), S.d = d → S.Ok →
  ∀ (r : ℕ) (b : Fin r → Fin g → ℂ), S.NNBasis q b →
  ∀ (M : ℕ) (Sk : Fin M → Setup g) (e : Fin M → (Fin g → ℂ) → ℂ) (t : Fin M → Fin g → ℂ) (c : Fin M → ℂ),
    (∀ k, (Sk k).d = d ∧ (Sk k).Hm = S.Hm ∧ (Sk k).Ok ∧ EqAtQ q S.La (Sk k).La) →
    (∀ k, (Sk k).IsTheta (e k) ∧ (Sk k).AlgJets δ (e k) ∧ (Sk k).PrimeTo q (t k)) →
    (∀ k, c k ∈ Qbar) → (∀ i k, b i ∈ (Sk k).La) →
  ∃ (ν : Fin M → C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]) (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]),
    (∀ k, MomentProperty lam Ω δ (Sk k) b (fun _ : Fin 0 => 0) (ν k) (e k) ∧
      AveragedMomentProperty lam Ω δ (Sk k) b (fun _ : Fin 0 => 0) (ν k) (e k)) ∧
    (∀ C : ℝ, 0 ≤ C → (∀ k, ‖lamA lam (c k)‖ * ‖ν k‖ ≤ C) → ‖μ‖ ≤ C) ∧
    MomentProperty lam Ω δ S b t μ (fun z => ∑ k, c k * opU S.Hm (t k) (e k) z) ∧
      AveragedMomentProperty lam Ω δ S b t μ (fun z => ∑ k, c k * opU S.Hm (t k) (e k) z)
end Formalism.L2.Ker.JMB


