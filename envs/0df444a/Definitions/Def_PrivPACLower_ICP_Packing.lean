-- Prove2me | Definitions.Def_PrivPACLower_ICP_Packing
-- name    : PrivPACLower_ICP_Packing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:46:59.710245+00:00
-- url     : https://prove2.me/theorems/78caf646-cbf8-4fe9-b5e3-19919c285d3e
-- title:
--   Independent class packing, ICP, padding points and block databases
-- statement:
--   Let $G_i\subseteq\{0,1\}^{Y_i}$ be nonempty classes, indexed by $i\in\{1,\ldots,k\}$, and let $\Phi_i:Y_i\to X$. They pack independently into a nonempty $H$ via these maps when each map is injective, their images are pairwise disjoint, and
--
--   $$\forall(g_i)\in\prod_iG_i,\quad\exists h\in H,\quad\forall i,y,\ h(\Phi_i(y))=g_i(y).$$
--
--   For an arbitrary collection $\mathcal G$ of classes, the independent class packing cost is
--
--   $$\operatorname{ICP}_{\varepsilon,\delta}(H,\mathcal G)=\sup_{(G_1,\ldots,G_k)\sqsubseteq H,\ G_i\in\mathcal G}\sum_i m_{\rm priv}(G_i;\varepsilon,\delta,\alpha_0,1/4).$$
--
--   Only finite domains $Y_i$ enter this supremum. The value lies in the extended nonnegative reals. A padding point $(x_0,y_0)$ permits every component tuple to have an extension that also labels $x_0$ by $y_0$. Conditioning one component at a point means retaining exactly its hypotheses with that label. Block costs sum the truncated quantities $(s_i-1)_+$. Database concatenation lists each block in order; appending copies adds the chosen labeled point.
--
--   These definitions preserve the maps used to attest packability and serve the padding and direct-sum statements.
--
--   **Formalization Note** Finite domains in the collection are small types; every finite domain has such a representative. Families use $\mathrm{Fin}\,k$, with zero-based indices. The empty family is allowed; its cost is zero. Extended costs preserve infinity.
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 5, 14, Definitions 1, 2 and 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

def PackingVia {X : Type*} {k : ℕ} {Y : Fin k → Type*}
    (H : Set (X → Bool)) (Gs : ∀ i, Set (Y i → Bool)) (Φ : ∀ i, Y i → X) : Prop :=
  H.Nonempty ∧ (∀ i, (Gs i).Nonempty) ∧ (∀ i, Function.Injective (Φ i)) ∧
    (∀ i j, i ≠ j → Disjoint (Set.range (Φ i)) (Set.range (Φ j))) ∧
    ∀ g : ∀ i, Y i → Bool, (∀ i, g i ∈ Gs i) →
      ∃ h ∈ H, ∀ i y, h (Φ i y) = g i y

def PaddingPoint {X : Type*} {k : ℕ} {Y : Fin k → Type*}
    (H : Set (X → Bool)) (Gs : ∀ i, Set (Y i → Bool))
    (Φ : ∀ i, Y i → X) (z : X × Bool) : Prop :=
  ∀ g : ∀ i, Y i → Bool, (∀ i, g i ∈ Gs i) →
    ∃ h ∈ H, (∀ i y, h (Φ i y) = g i y) ∧ h z.1 = z.2

/-- An arbitrary collection; only its members on finite domains enter ICP. -/
abbrev ClassCollection := (Y : Type) → Set (Set (Y → Bool))

noncomputable def ICP {X : Type*} (α₀ ε δ : ℝ) (H : Set (X → Bool))
    (G : ClassCollection) : ℝ≥0∞ :=
  ⨆ (k : ℕ) (Y : Fin k → Type) (_ : ∀ i, Fintype (Y i))
    (Gs : ∀ i, Set (Y i → Bool)) (_ : ∀ i, Gs i ∈ G (Y i))
    (Φ : ∀ i, Y i → X) (_ : PackingVia H Gs Φ),
      ∑ i, costReal (mpriv (Gs i) ε δ α₀ (1/4))

def conditionedClass {Y : Type*} (G : Set (Y → Bool)) (y : Y) (b : Bool) : Set (Y → Bool) :=
  {g ∈ G | g y = b}

noncomputable def restrictComponent {k : ℕ} {Y : Fin k → Type*}
    (Gs : ∀ i, Set (Y i → Bool)) (j : Fin k) (y : Y j) (b : Bool) :
    ∀ i, Set (Y i → Bool) :=
  Function.update Gs j (conditionedClass (Gs j) y b)

/-- The paper's `∑ i, (s_i - 1)_+` (Lemma 6(1), Lemma 7): the truncated subtraction is
applied to each summand, `s_i = mpriv (Gs i) ε δ α₀ (1/4)`; `⊤ - 1 = ⊤`. -/
noncomputable def blockCost {k : ℕ} {Y : Fin k → Type*}
    (Gs : ∀ i, Set (Y i → Bool)) (ε δ α₀ : ℝ) : ℕ∞ :=
  ∑ i, (mpriv (Gs i) ε δ α₀ (1/4) - 1)

/-- Lexicographic concatenation: block i, then position inside block i. -/
def concatDB {X : Type*} {k : ℕ} {Y : Fin k → Type*}
    (Φ : ∀ i, Y i → X) (q : Fin k → ℕ)
    (S : ∀ i, Fin (q i) → Y i × Bool) : Fin (∑ i, q i) → X × Bool :=
  fun t => let p := finSigmaFinEquiv.symm t; (Φ p.1 (S p.1 p.2).1, (S p.1 p.2).2)

def appendCopies {X : Type*} {n : ℕ} (S : Fin n → X × Bool)
    (z : X × Bool) (r : ℕ) : Fin (n+r) → X × Bool :=
  Fin.addCases S (fun _ => z)

end PrivPACLower.ICP


