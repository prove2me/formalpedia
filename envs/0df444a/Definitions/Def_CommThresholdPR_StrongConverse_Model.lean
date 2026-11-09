-- Prove2me | Definitions.Def_CommThresholdPR_StrongConverse_Model
-- name    : CommThresholdPR_StrongConverse_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:57.894415+00:00
-- url     : https://prove2.me/theorems/868f647c-2bcc-45e8-b016-d49bcc773057
-- title:
--   Total relations, independent repetition and operational information complexity
-- statement:
--   A total relation $g\subseteq X\times Y\times A\times B$ admits a valid output for each input pair. The law $\mu^{\otimes n}$ samples independent copies of the joint input law, allowing correlation within each pair; $g^n$ accepts exactly when every coordinate accepts. Define protocol error by its actual failure probability and
--   $$\operatorname{IC}_{\mu}(g,\varepsilon)=\inf_{\pi:\operatorname{err}_{\mu}(\pi)\le\varepsilon}\operatorname{IC}_{\mu}(\pi),\qquad
--   \operatorname{err}_{\mu}(R)=\inf_{\pi:\operatorname{IC}_{\mu}(\pi)\le R}\operatorname{err}_{\mu}(\pi).$$
--   The infima range over the full protocol type, with arbitrary finite randomness and depth. The guarded real infimum uses zero outside its nonempty bounded-below domain; on the source domain exchanging inputs and constant-output protocols supply witnesses, and nonnegativity supplies lower bounds. These are solver obligations, not assumptions.
--
--   The zero-message value is the maximum success over deterministic local output maps, independently of information complexity. Its gap is $\eta=1-\omega(g,\mu)$. The alphabet logarithms, $\delta(n,p)$ and both explicit exponent formulas are computed directly. This definition asserts no continuity, budget identity or success bound.
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), §§2.1–2.3, pp. 7–8, (5)–(8); (14)–(15), p. 9; (33), p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Protocols

noncomputable section

namespace CommThresholdPR.StrongConverse

/-- Total relations, §2.1 p.7. No correctness condition is put in a protocol. -/
structure TotalRelation (X Y A B : Type) where
  accepts : X → Y → A → B → Prop
  total : ∀ x y, ∃ a b, accepts x y a b

variable {X Y A B : Type}

def repeated (g : TotalRelation X Y A B) (n : ℕ) :
    TotalRelation (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  accepts x y a b := ∀ i, g.accepts (x i) (y i) (a i) (b i)
  total x y := by
    classical
    choose a b h using fun i => g.total (x i) (y i)
    exact ⟨a, b, h⟩

/-- Independent copies of the JOINT law. The two inputs of one copy may correlate. -/
def iidPairs (μ : PMF (X × Y)) : (n : ℕ) → PMF (Fin n → X × Y)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | n + 1 => (iidPairs μ n).bind fun z => μ.map fun xy => Fin.snoc z xy

def inputPower (μ : PMF (X × Y)) (n : ℕ) : PMF ((Fin n → X) × (Fin n → Y)) :=
  (iidPairs μ n).map fun z => (fun i => (z i).1, fun i => (z i).2)

def lawError [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {V : Type} [Fintype V] (g : TotalRelation X Y A B)
    (p : PMF (Record X Y A B V)) : ℝ :=
  prob p (fun z => ¬ g.accepts z.x z.y z.a z.b)

def protocolError [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (g : TotalRelation X Y A B) (μ : PMF (X × Y)) (π : Protocol X Y A B) : ℝ :=
  lawError g (π.law μ)

/-- Guarded real infimum. For the source domains the protocol sets are nonempty
and bounded below: exchange inputs to attain zero error; constant-output leaves
have information zero; all errors and information costs are nonnegative.
Those facts are proof obligations, not fields or hypotheses of this definition. -/
def operationalInf (S : Set ℝ) : ℝ := by
  classical
  exact if S.Nonempty ∧ BddBelow S then sInf S else 0

def informationComplexity [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (g : TotalRelation X Y A B) (μ : PMF (X × Y)) (ε : ℝ) : ℝ :=
  operationalInf {c | ∃ π : Protocol X Y A B,
    protocolError g μ π ≤ ε ∧ c = π.info μ}

def errorAtRate [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (g : TotalRelation X Y A B) (μ : PMF (X × Y)) (R : ℝ) : ℝ :=
  operationalInf {e | ∃ π : Protocol X Y A B,
    π.info μ ≤ R ∧ e = protocolError g μ π}

def gameValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (g : TotalRelation X Y A B) (μ : PMF (X × Y)) : ℝ :=
  sSup {s | ∃ (a : X → A) (b : Y → B), s = prob μ (fun xy => g.accepts xy.1 xy.2 (a xy.1) (b xy.2))}

def gap [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (g : TotalRelation X Y A B) (μ : PMF (X × Y)) : ℝ := 1 - gameValue g μ

def logInput (X Y : Type) [Fintype X] [Fintype Y] : ℝ :=
  Real.logb 2 (Fintype.card X * Fintype.card Y : ℕ)

def logOutput (A B : Type) [Fintype A] [Fintype B] : ℝ :=
  Real.logb 2 (Fintype.card A * Fintype.card B : ℕ)

def delta (n : ℕ) (p : ℝ) : ℝ :=
  Real.sqrt (Real.log 2 / (2 * n) * Real.logb 2 (1 / p))

/-- Equations (14) and (15); the theorem supplies the domain and positivity,
including the nonzero output logarithm. -/
def exponent [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (g : TotalRelation X Y A B) (μ : PMF (X × Y)) (R : ℝ) : ℝ :=
  if R = 0 then gap g μ ^ 3 / (128 * logOutput A B) else
    (2 : ℝ) ^ (-28 : ℤ) * min (errorAtRate g μ R ^ 3 / logOutput A B)
      (errorAtRate g μ R ^ 4 * R ^ 2 / (1 + logInput X Y) ^ 4)

end CommThresholdPR.StrongConverse


