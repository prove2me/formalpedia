-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Codes
-- name    : RandomStreamCI_CodeIntersection_Codes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:29:00.050281+00:00
-- url     : https://prove2.me/theorems/aa800de1-7fa1-4621-b190-cb5e3dc193f2
-- title:
--   Folded code families, linear duals and quantitative family properties
-- statement:
--   Bare parameters specify a finite field with publicly named elements, folding size, polynomial degree cutoff, evaluation embedding and multiplier. The code is the published image of degree-bounded grouped polynomial evaluation. The dual is the orthogonal complement over the base field after unfolding folded symbols. The independent noise law assigns half its mass to zero and equal remaining mass to nonzero symbols.
--
--   $$D(0)=\tfrac12,\qquad D(a)=\frac1{2(|\Sigma|-1)}\quad(a\ne0).$$
--
--   The family-property predicate collects the exact asymptotics, explicit generator, total-list recovery and one polynomial-time decoder's simultaneous good-noise event from Proposition 7. These are conclusions to prove, not fields of the bare code parameters. Small blocklengths carry data but all asymptotic obligations are eventual.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Proposition 7 and equations (13)–(14), pp. 8–9

import Definitions.Def_Yukon_5ee536a65c1a8881b97bd895
import Definitions.Def_RandomStreamCI_CodeIntersection_Stream
import Definitions.Def_RandomStreamCI_CodeIntersection_Computation

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Public labels 0, …, q-1 for the q base-field elements. This is a bare type
synonym of `Fin q` (a `def`, not an `abbrev`), so the mod-q arithmetic of `Fin q`
is NOT inherited: the only arithmetic on labels is the bundled field structure. -/
def FieldLabel (q : ℕ) : Type := Fin q

instance (q : ℕ) : Fintype (FieldLabel q) := inferInstanceAs (Fintype (Fin q))
instance (q : ℕ) : DecidableEq (FieldLabel q) := inferInstanceAs (DecidableEq (Fin q))

/-- The public number of a label. -/
def FieldLabel.val {q : ℕ} (a : FieldLabel q) : ℕ := Fin.val (show Fin q from a)

/-- All labels, in increasing order. -/
def FieldLabel.all (q : ℕ) : List (FieldLabel q) := List.finRange q

/-- Bare folded-code parameters. No recovery, decoding or growth claim is
part of this data type. The base field F_q is a field structure on the q labels. -/
structure CodeParameters (n : ℕ) where
  q : ℕ
  baseField : Field (FieldLabel q)
  m : ℕ
  degree : ℕ
  domain : Fin n ↪ FieldLabel q
  multiplier : FieldLabel q

attribute [instance] CodeParameters.baseField

namespace CodeParameters

abbrev Alphabet {n : ℕ} (P : CodeParameters n) := Fin P.m → FieldLabel P.q
abbrev Words {n : ℕ} (P : CodeParameters n) := Fin n → P.Alphabet

/-- Reuse of the published grouped-evaluation image, with the actual domain
embedding and multiplier (no abstract code satisfying promises). -/
def code {n : ℕ} (P : CodeParameters n) : Finset P.Words :=
  (ReedSolomon.Folded.frsCode P.domain P.degree P.m P.multiplier).carrier.toFinset

/-- Duality is over F_q, after unfolding every folded field entry. -/
def dual {n : ℕ} (P : CodeParameters n) : Finset P.Words :=
  Finset.univ.filter (fun x => ∀ c ∈ P.code, (∑ i, ∑ j, x i j * c i j) = 0)

/-- Public finite description: dimensions, domain, multiplier, and all field
operation tables. Its size is polynomial because q=Theta(n^2). -/
def description {n : ℕ} (P : CodeParameters n) : List Bool :=
  encodeNats ([P.q, P.m, P.degree, P.multiplier.val, (0 : FieldLabel P.q).val,
      (1 : FieldLabel P.q).val] ++
    (List.finRange n).map (fun i => (P.domain i).val) ++
    (FieldLabel.all P.q).flatMap (fun a => (FieldLabel.all P.q).flatMap (fun b =>
      [(a + b).val, (a * b).val])) ++
    (FieldLabel.all P.q).flatMap (fun a => [(-a).val, (a⁻¹).val]))

def encodeWord {n : ℕ} (P : CodeParameters n) (x : P.Words) : List Bool :=
  encodeNats ([n, P.m, P.q] ++
    (List.finRange n).flatMap (fun i => (List.finRange P.m).map (fun j => (x i j).val)))

/-- Product noise from Proposition 7 (14). Only m>0 is used in that proposition,
so Q>1 and the denominator 2(Q-1) is positive. -/
def noiseWeight {n : ℕ} (P : CodeParameters n) (e : P.Words) : ℝ :=
  ∏ i, if e i = 0 then (1 / 2 : ℝ)
    else 1 / (2 * ((Fintype.card P.Alphabet : ℝ) - 1))

end CodeParameters

abbrev CodeFamily := (n : ℕ) → CodeParameters n

/-- Explicit generation for every sufficiently large integer blocklength.
Small lengths are harmless data and are never used by the asymptotic assertions. -/
def ExplicitFamily (F : CodeFamily) : Prop :=
  ∃ N : ℕ, PolyComputes (fun n : {n : ℕ // N ≤ n} => encodeNat n.val)
    (fun n => (F n.val).description)

/-- Standard eventual two-sided bounds, with constants uniform in n. -/
def ThetaGrowth (f g : ℕ → ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, ∀ n ≥ N,
    a * g n ≤ f n ∧ f n ≤ b * g n

def UpperGrowth (f g : ℕ → ℝ) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ, ∀ n ≥ N, f n ≤ b * g n

/-- Subexponential list size, with an arbitrary positive exponent and a
separate threshold, rather than a single finite test blocklength. -/
def Subexponential (L : ℕ → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, log₂ (L n) ≤ δ * n

/-- All conclusions of Proposition 7, expressed as a predicate to be proved,
never as fields of the input code data. Includes one uniform polynomial-time
decoder with simultaneous correctness for every dual codeword on a good noise. -/
def FamilyProperties (F : CodeFamily) (c c' : ℝ) : Prop :=
  ExplicitFamily F ∧
  ThetaGrowth (fun n => (F n).q) (fun n => (n : ℝ)^2) ∧
  ThetaGrowth (fun n => (F n).m) (fun n => n) ∧
  ThetaGrowth (fun n => log₂ (Fintype.card (F n).Alphabet))
    (fun n => n * log₂ n) ∧
  UpperGrowth (fun n => log₂ (F n).code.card) (fun n => (n : ℝ)^2 * log₂ n) ∧
  ∃ (ρ : ℝ) (ℓ L : ℕ → ℕ), 0 < ρ ∧ ρ < 1 ∧
    ThetaGrowth (fun n => log₂ (ℓ n)) (fun n => (n : ℝ)^c) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ d : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      log₂ (L n) ≤ K * (n : ℝ)^c' * (log₂ n)^d) ∧
    Subexponential L ∧
    ∃ (decode : (n : ℕ) → (F n).Words → (F n).Words) (a : ℝ), 0 < a ∧
      (∃ N : ℕ, PolyComputes
        (fun x : (n : {n : ℕ // N ≤ n}) × (F n.val).Words => (F x.1.val).encodeWord x.2)
        (fun x => (F x.1.val).encodeWord (decode x.1.val x.2))) ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N,
        0 < (F n).m ∧ (F n).degree ≤ n * (F n).m ∧
        Function.Injective (fun ij : Fin n × Fin (F n).m =>
          (F n).domain ij.1 * (F n).multiplier ^ ij.2.val) ∧
        ListRecoverable (F n).code ρ (ℓ n : ℝ) (L n : ℝ) ∧
        1 - (2 : ℝ)^(-a * n) ≤ eventMass ((F n).noiseWeight)
          (fun e => ∀ x ∈ (F n).dual, decode n (x + e) = x)

end RandomStreamCI.CodeIntersection


