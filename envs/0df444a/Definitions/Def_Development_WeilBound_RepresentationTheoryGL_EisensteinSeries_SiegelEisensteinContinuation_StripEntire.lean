-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
-- name    : Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:06.510797+00:00
-- url     : https://prove2.me/theorems/89c6bc54-a378-44e0-b818-051ae128fa6e
-- title:
--   Strip Entire
-- statement:
--   Definitions and structural lemmas for Strip Entire, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/EisensteinSeries/SiegelEisensteinContinuation/StripEntire.lean

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
open Filter Topology
namespace PositivityTheory.RgEis
section Tube
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
def tube (Ω : Set (ℝ × ℝ)) : Set (ℂ × ℂ) := {l | (l.1.re, l.2.re) ∈ Ω}
def LineHol (F : ℂ × ℂ → X) (U : Set (ℂ × ℂ)) : Prop :=
  ∀ p v : ℂ × ℂ, DifferentiableOn ℂ (fun τ : ℂ => F (p + τ • v)) {τ | p + τ • v ∈ U}
structure TubeGood {T : Type} [TopologicalSpace T] (F : ℂ × ℂ → T → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : ∀ g, LineHol (F · g) (tube Ω)
  cont : ContinuousOn (fun y : (ℂ × ℂ) × T => F y.1 y.2) (tube Ω ×ˢ Set.univ)
  bdd : ∀ C ⊆ Ω, IsCompact C → ∀ g, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ l ∈ tube C, ∀ g' ∈ U, ‖F l g'‖ ≤ M
def LeftGood (f : ℂ → X) (a : ℝ) : Prop :=
  DifferentiableOn ℂ f {z | z.re < a} ∧ ∀ b c : ℝ, c < a → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖f z‖ ≤ M
def StripEntire (f : ℂ → X) : Prop :=
  Differentiable ℂ f ∧ ∀ b c : ℝ, ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖f z‖ ≤ M
end Tube
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
def Iwa (P K : Subgroup G) : Prop := ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k
structure IsHt (Γ K P : Subgroup G) (η : G → ℝ) : Prop where
  left : ∀ p ∈ P, ∀ g, η (p * g) = η p + η g
  right : ∀ g, ∀ k ∈ K, η (g * k) = η g
  rat : ∀ γ ∈ Γ, γ ∈ P → η γ = 0
  cont : Continuous η
structure IsCh (Γ P : Subgroup G) (c : G → ℂ) : Prop where
  mul : ∀ p ∈ P, ∀ q ∈ P, c (p * q) = c p * c q
  norm : ∀ p ∈ P, ‖c p‖ = 1
  rat : ∀ γ ∈ Γ, γ ∈ P → c γ = 1
  cont : ContinuousOn c P
structure IsPar (Γ K P : Subgroup G) (c : G → ℂ) : Prop where
  closed : IsClosed (P : Set G)
  iwa : Iwa P K
  ch : IsCh Γ P c
def secSp (K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) : Submodule ℂ W where
  carrier := {w | ∀ r : K, (r : G) ∈ P → c r • ρ r w = w}
  add_mem' := fun {a b} ha hb r hr => by rw [map_add, smul_add, ha r hr, hb r hr]
  zero_mem' := fun r _ => by simp
  smul_mem' := fun a w hw r hr => by rw [map_smul, smul_comm, hw r hr]
open Classical in

def sec (K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (g : G) : W →L[ℂ] W :=
  if h : ∃ k : K, g * (k : G)⁻¹ ∈ P then c (g * (h.choose : G)⁻¹) • ρ h.choose⁻¹ else 0
abbrev Cos (P Γ : Subgroup G) : Type := Quotient (QuotientGroup.rightRel (P.subgroupOf Γ))
def rep {P Γ : Subgroup G} (q : Cos P Γ) : G := (Quotient.out q).1
def eis (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (w : W) : W :=
  ∑' q : Cos P Γ, Complex.exp (Λ (rep q * g)) • sec K P c ρ (rep q * g) w
def Conv (Γ P : Subgroup G) (l : G → ℝ) : Prop := ∀ g, Summable fun q : Cos P Γ => Real.exp (l (rep q * g))
def pos (Γ P : Subgroup G) (l : G → ℝ) (g : G) : ℝ := ∑' q : Cos P Γ, Real.exp (l (rep q * g))
structure Wall (Γ K P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ) (ρ : K →* (W →L[ℂ] W)) (L : Submodule ℂ W)
    (R : ℝ) (D : ℂ → ℂ) (Op : ℂ → (L →L[ℂ] secSp K P' c ρ)) (H : ℂ → G → (L →L[ℂ] W)) : Prop where
  le : L ≤ secSp K P c ρ
  pos : 0 ≤ R
  convR : ∀ x : ℝ, R < x → Conv Γ P fun g => x * η g
  convL : ∀ x : ℝ, x < -R → Conv Γ P' fun g => β g - x * η' g
  dEnt : StripEntire D
  dNe : ∃ z, D z ≠ 0
  op : LeftGood Op (-R)
  hol : ∀ g, Differentiable ℂ (H · g)
  cont : Continuous fun y : ℂ × G => H y.1 y.2
  bdd : ∀ (b a : ℝ) (g : G), ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g' ∈ U, ‖H z g'‖ ≤ M
  eqR : ∀ z : ℂ, R < z.re → ∀ (g : G) (w : L), H z g w = D z • eis Γ K P c ρ (fun x => z * η x) g w
  eqL : ∀ z : ℂ, z.re < -R → ∀ (g : G) (w : L), H z g w = eis Γ K P' c ρ (fun x => β x - z * η' x) g (Op z w)
def HasWall (Γ K P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ) (ρ : K →* (W →L[ℂ] W)) : Prop :=
  ∃ R D Op H, Wall Γ K P P' c η η' β ρ (secSp K P c ρ) R D Op H
def HasFirst (Γ K S P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ) (ρ : K →* (W →L[ℂ] W)) : Prop :=
  ∃ R D Op H, Wall Γ K P P' c η η' β ρ (secSp K S c ρ) R D Op H ∧
    (∃ a : ℂ, a ≠ 0 ∧ ∀ g (w : secSp K S c ρ), H 0 g w = a • sec K S c ρ g w) ∧
    ∃ O : ℂ → (secSp K S c ρ →L[ℂ] secSp K P' c ρ), LeftGood O (1 / 2) ∧ ∀ z : ℂ, z.re < -R → Op z = z • O z
def HasLast (Γ K S P P' : Subgroup G) (c : G → ℂ) (η η' β ξ : G → ℝ) (N : ℝ) (ρ : K →* (W →L[ℂ] W)) : Prop :=
  ∃ R D Op H, Wall Γ K P P' c η η' β ρ (secSp K P c ρ) R D Op H ∧
    (∃ d : ℂ → ℂ, StripEntire d ∧ d N ≠ 0 ∧ ∀ z, D z = (z - N) * d z) ∧
    ∃ T : secSp K P c ρ →L[ℂ] secSp K S c ρ, ∀ g w, H N g w = Complex.exp (ξ g) • sec K S c ρ g (T w)
def ForRep (Q : ∀ {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (K : Subgroup G), (K →* (W →L[ℂ] W)) → Prop) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (W : Type)
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (K : Subgroup G) (ρ : K →* (W →L[ℂ] W)),
    IsCompact (K : Set G) → Continuous ρ → Q K ρ
def IdTube : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω Ω' : Set (ℝ × ℝ)) (F F' : ℂ × ℂ → X),
    IsOpen Ω → Convex ℝ Ω → IsOpen Ω' → Ω'.Nonempty → Ω' ⊆ Ω → LineHol F (tube Ω) → LineHol F' (tube Ω) →
    Set.EqOn F F' (tube Ω') → Set.EqOn F F' (tube Ω)
def TubeChain : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : Type) [TopologicalSpace T]
    [FirstCountableTopology T] (m : ℕ) (Ω : Fin (m + 1) → Set (ℝ × ℝ)) (F : Fin (m + 1) → ℂ × ℂ → T → X),
    (∀ i, IsOpen (Ω i) ∧ Convex ℝ (Ω i) ∧ TubeGood (F i) (Ω i)) →
    (∀ i : Fin m, ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω i.castSucc ∩ Ω i.succ ∧
      ∀ l ∈ tube V, ∀ g, F i.castSucc l g = F i.succ l g) →
    (∀ x : ℝ × ℝ, ∃ i j, ∃ a ∈ Ω i, ∃ b ∈ Ω j, x = midpoint ℝ a b) →
    ∃ Φ : ℂ × ℂ → T → X, TubeGood Φ Set.univ ∧
      ∀ i, ∀ l ∈ tube (Ω i), ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F i l g
def SecLaw : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ (Γ P : Subgroup G) (c : G → ℂ), IsPar Γ K P c →
  (∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w) ∧
  (∀ w ∈ secSp K P c ρ, Continuous fun g => sec K P c ρ g w) ∧
  ∃ M : ℝ, ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖
def HtLip : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ K P : Subgroup G) (η : G → ℝ),
    IsCompact (K : Set G) → Iwa P K → IsHt Γ K P η → ∀ C : Set G, IsCompact C → ∃ M : ℝ, ∀ g, ∀ u ∈ C, |η (g * u) - η g| ≤ M
def PiLocalization₂ : Prop :=
  ∀ (G : Type) [Group G] (X : Type) [NormedAddCommGroup X] [CompleteSpace X] (P Δ Γ : Subgroup G) (f : G → X),
    Δ ≤ Γ → (∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x) → ∀ g : G,
    (Summable fun q : Cos P Γ => ‖f (rep q * g)‖) →
    (∀ x ∈ Γ, Summable fun q : Cos P Δ => ‖f (rep q * (x * g))‖) ∧
    (Summable fun r : Cos Δ Γ => ∑' q : Cos P Δ, ‖f (rep q * (rep r * g))‖) ∧
    ∑' q : Cos P Γ, f (rep q * g) = ∑' r : Cos Δ Γ, ∑' q : Cos P Δ, f (rep q * (rep r * g))
def WallLaw : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ (Γ P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ)
  (L : Submodule ℂ W) R D Op H, IsPar Γ K P c → IsPar Γ K P' c → IsHt Γ K P η → IsHt Γ K P' η' → IsHt Γ K P' β →
  Wall Γ K P P' c η η' β ρ L R D Op H →
  (∀ z, ∀ γ ∈ Γ, ∀ g, H z (γ * g) = H z g) ∧ (∀ z g (k : K) (w : L), H z (g * k) w = ρ k⁻¹ (H z g w)) ∧
  ∀ a b : ℝ, R < a → b < -R → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g,
    ‖H z g‖ ≤ M * (pos Γ P (fun x => a * η x) g + pos Γ P' (fun x => β x - b * η' x) g)
def outer (Γ Δ : Subgroup G) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (ξ : G → ℝ) (H : ℂ → G → X)
    (l : ℂ × ℂ) (g : G) : X := ∑' r : Cos Δ Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)
def Cross : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ (Γ Q P P' : Subgroup G) (c : G → ℂ) (η η' β ξ : G → ℝ)
  (L : Submodule ℂ W) R D Op H (Ω : Set (ℝ × ℝ)), P ≤ Q → P' ≤ Q → IsPar Γ K P c → IsPar Γ K P' c → IsHt Γ K P η →
  IsHt Γ K P' η' → IsHt Γ K P' β → IsHt Γ K Q ξ → Wall (Γ ⊓ Q) K P P' c η η' β ρ L R D Op H → IsOpen Ω →
  (∀ x ∈ Ω, ∃ a b ε : ℝ, 0 < ε ∧ R < a ∧ b < -R ∧ b < x.1 ∧ x.1 < a ∧ ∀ t : ℝ, |t - x.2| ≤ ε →
    Conv Γ P (fun g => a * η g + t * ξ g) ∧ Conv Γ P' fun g => β g - b * η' g + t * ξ g) →
  TubeGood (outer Γ (Γ ⊓ Q) ξ H) Ω ∧
  (∀ l ∈ tube Ω, ∀ g, Summable fun r : Cos (Γ ⊓ Q) Γ => ‖Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)‖) ∧
  (∀ l ∈ tube Ω, R < l.1.re → Conv Γ P (fun g => l.1.re * η g + l.2.re * ξ g) → ∀ g (w : L),
    outer Γ (Γ ⊓ Q) ξ H l g w = D l.1 • eis Γ K P c ρ (fun x => l.1 * η x + l.2 * ξ x) g w) ∧
  ∀ l ∈ tube Ω, l.1.re < -R → Conv Γ P' (fun g => β g - l.1.re * η' g + l.2.re * ξ g) → ∀ g (w : L),
    outer Γ (Γ ⊓ Q) ξ H l g w = eis Γ K P' c ρ (fun x => β x - l.1 * η' x + l.2 * ξ x) g (Op l.1 w)
def Gallery : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => FirstCountableTopology G →
  ∀ (Γ S A B Q₁ Q₂ : Subgroup G) (c : G → ℂ) (h a b : G → ℝ) (N : ℝ), A ≤ S → B ≤ S → A ≤ Q₁ → B ≤ Q₂ →
  IsPar Γ K S c → IsPar Γ K A c → IsPar Γ K B c → IsHt Γ K S h → IsHt Γ K Q₁ a → IsHt Γ K Q₂ (fun g => h g + b g) →
  (∃ R : ℝ, (∀ y : ℝ, R < y → Conv Γ S fun g => y * h g) ∧
    (∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g) ∧
    ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) →
  HasFirst (Γ ⊓ S) K S A B c a b (fun g => h g + N * b g) ρ →
  HasWall (Γ ⊓ Q₂) K B B c (fun g => -b g) (fun g => -b g) (fun g => -b g) ρ →
  HasWall (Γ ⊓ S) K B A c b a (fun g => N * a g - h g) ρ →
  HasWall (Γ ⊓ Q₁) K A A c (fun g => h g - a g) (fun g => h g - a g) (fun g => (N - 1) * (h g - a g)) ρ →
  HasLast (Γ ⊓ S) K S A B c a b (fun g => h g + N * b g) h N ρ →
  HasWall Γ K S S c h h (fun g => N * h g) ρ
structure IsLevi {G' : Type} [Group G'] [TopologicalSpace G'] (Γ K Q : Subgroup G) (Γ' K' : Subgroup G') (π : Q →* G')
    (ι : G' →* Q) (c₀ : G → ℂ) : Prop where
  contπ : Continuous π
  contι : Continuous ι
  sect : ∀ m, π (ι m) = m
  par : IsPar Γ K Q c₀
  triv : ∀ m, c₀ (ι m) = 1
  πK : ∀ q : Q, (q : G) ∈ K → π q ∈ K'
  ιK : ∀ m ∈ K', (ι m : G) ∈ K
  πΓ : ∀ q : Q, (q : G) ∈ Γ → π q ∈ Γ'
  ιΓ : ∀ m ∈ Γ', (ι m : G) ∈ Γ
structure IsPull {G' : Type} [Group G'] (Q P : Subgroup G) (P' : Subgroup G') (π : Q →* G') (c₀ c : G → ℂ) (c' : G' → ℂ) :
    Prop where
  mem : ∀ g, g ∈ P ↔ ∃ hg : g ∈ Q, π ⟨g, hg⟩ ∈ P'
  ch : ∀ q : Q, π q ∈ P' → c q = c₀ q * c' (π q)
def PullHt {G' : Type} [Group G'] (K Q : Subgroup G) (π : Q →* G') (η : G → ℝ) (η' : G' → ℝ) : Prop :=
  ∀ (q : Q), ∀ k ∈ K, η ((q : G) * k) = η' (π q)
def AllRep (K : Subgroup G) (Q : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W], (K →* (W →L[ℂ] W)) → Prop) : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (ρ : K →* (W →L[ℂ] W)), Continuous ρ → Q ρ
def Transfer : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ (G' : Type) [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G'] [T2Space G'] [LocallyCompactSpace G'] (Γ Q S P₁ P₂ : Subgroup G) (Γ' K' S' P₁' P₂' : Subgroup G')
  (π : Q →* G') (ι : G' →* Q) (c₀ c : G → ℂ) (c' : G' → ℂ) (η₁ η₂ β ξ : G → ℝ) (η₁' η₂' β' ξ' : G' → ℝ) (N : ℝ),
  IsCompact (K' : Set G') → IsLevi Γ K Q Γ' K' π ι c₀ → IsPull Q S S' π c₀ c c' → IsPull Q P₁ P₁' π c₀ c c' →
  IsPull Q P₂ P₂' π c₀ c c' → IsPar Γ' K' S' c' → IsPar Γ' K' P₁' c' → IsPar Γ' K' P₂' c' → IsHt Γ' K' P₁' η₁' →
  IsHt Γ' K' P₂' η₂' → IsHt Γ' K' P₂' β' → PullHt K Q π η₁ η₁' → PullHt K Q π η₂ η₂' → PullHt K Q π β β' →
  PullHt K Q π ξ ξ' →
  ((AllRep K' fun ρ' => HasWall Γ' K' P₁' P₂' c' η₁' η₂' β' ρ') → HasWall (Γ ⊓ Q) K P₁ P₂ c η₁ η₂ β ρ) ∧
  ((AllRep K' fun ρ' => HasFirst Γ' K' S' P₁' P₂' c' η₁' η₂' β' ρ') → HasFirst (Γ ⊓ Q) K S P₁ P₂ c η₁ η₂ β ρ) ∧
  ((AllRep K' fun ρ' => HasLast Γ' K' S' P₁' P₂' c' η₁' η₂' β' ξ' N ρ') → HasLast (Γ ⊓ Q) K S P₁ P₂ c η₁ η₂ β ξ N ρ)
end PositivityTheory.RgEis


