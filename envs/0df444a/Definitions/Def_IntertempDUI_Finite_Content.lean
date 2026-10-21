-- Prove2me | Definitions.Def_IntertempDUI_Finite_Content
-- name    : IntertempDUI_Finite_Content
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:05.874532+00:00
-- url     : https://prove2.me/theorems/89b07940-cbb7-4c89-ac3c-1e15c6098c65
-- title:
--   Appendix B — normalized contents and the integrator
-- statement:
--   A **content** $\mu$ assigns values in $[0,1]$ to time spans, has $\mu(\mathcal T)=1$, and is additive on disjoint spans under the Boolean join. It has full support if each nonempty span has positive content and is nonatomic if arbitrarily small-content spans surround every time point. A real function is comeasurable when the interiors of its upper and lower level sets are spans.
--
--   $$I^{\mu}_{\mathcal S}[g]=\sup\left\{\sum_i r_i\mu(\mathcal S_i): (\mathcal S_i)_i\text{ partitions }\mathcal S,\ f|_{\mathcal S_i}=r_i,\ f\le g\text{ on }\mathcal S\right\}.$$
--
--   The content-utility representation (B7) compares trajectories by this integrator applied to $u\circ\alpha$. Its utility represents synchronic preference, and its formula covers both the induced span orders and the primitive interval orders of the intertemporal structure. These definitions provide the intermediate representation used by Theorem B2.
--
--   **Formalization Note** Simple functions may take arbitrary values on partition boundaries. The integrator is evaluated only for continuous comeasurable trajectory utilities in the representation theorem.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), pp. 25–26, (B1), (B4)–(B7); https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Axioms

namespace IntertempDUI.Finite

/-- The normalized finitely additive content of Appendix B, equation (B1). -/
def IsContent {T : ℝ} (μ : Set (Time T) → ℝ) : Prop :=
  μ Set.univ = 1 ∧
  (∀ S, IsTimeSpan S → 0 ≤ μ S ∧ μ S ≤ 1) ∧
  (∀ Q R, IsTimeSpan Q → IsTimeSpan R → Disjoint Q R →
    μ (join Q R) = μ Q + μ R)

/-- Full support is required only for nonempty spans. -/
def FullSupport {T : ℝ} (μ : Set (Time T) → ℝ) : Prop :=
  ∀ S, IsTimeSpan S → S.Nonempty → 0 < μ S

def Nonatomic {T : ℝ} (μ : Set (Time T) → ℝ) : Prop :=
  ∀ t : Time T, ∀ ε : ℝ, 0 < ε →
    ∃ S, IsTimeSpan S ∧ t ∈ S ∧ μ S < ε

/-- Appendix B's comeasurability criterion. -/
def Comeasurable {T : ℝ} (g : Time T → ℝ) : Prop :=
  ∀ r : ℝ,
    IsTimeSpan (interior {t | g t ≤ r}) ∧
    IsTimeSpan (interior {t | r ≤ g t})

/-- A finite partition in the Boolean algebra of regular-open time spans. -/
def IsPartition {T : ℝ} (S : Set (Time T)) {N : ℕ}
    (P : Fin N → Set (Time T)) : Prop :=
  (∀ i, IsTimeSpan (P i)) ∧
  (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
  S = interior (closure (⋃ i, P i))

/-- The simple-function lower sum (B4) and supremum (B5)–(B6).
The witness f is defined also on partition boundaries, where the source permits arbitrary values. -/
noncomputable def integrator {T : ℝ} (μ : Set (Time T) → ℝ)
    (S : Set (Time T)) (g : Time T → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (N : ℕ) (P : Fin N → Set (Time T)) (r : Fin N → ℝ)
      (f : Time T → ℝ), IsPartition S P ∧
      (∀ i, ∀ t ∈ P i, f t = r i) ∧
      (∀ t ∈ S, f t ≤ g t) ∧
      v = ∑ i, r i * μ (P i)}

/-- The content-utility representation (B7) on the paper's admissible trajectories. -/
def IsContentUtilityRep {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X)
    (u : X → ℝ) (μ : Set (Time T) → ℝ) : Prop :=
  Continuous u ∧ IsContent μ ∧
  (∀ x y : X, sy pref x y ↔ u y ≤ u x) ∧
  (∀ a ∈ A, Comeasurable (u ∘ a)) ∧
  (∀ S, IsTimeSpan S → ∀ a ∈ A, ∀ b ∈ A,
    induced A pref S a b ↔
      integrator μ S (u ∘ a) ≥ integrator μ S (u ∘ b)) ∧
  (∀ I, IsTimeInterval I → ∀ a ∈ A, ∀ b ∈ A,
    pref I a b ↔
      integrator μ I (u ∘ a) ≥ integrator μ I (u ∘ b))

end IntertempDUI.Finite


