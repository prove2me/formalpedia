-- Prove2me | Definitions.Def_MoserSchneckenreither_Typing
-- name    : MoserSchneckenreither_Typing
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T08:56:15.225233+00:00
-- url     : https://prove2.me/theorems/0ca398d6-8f77-483a-a0b5-18ca3953c3bb
-- title:
--   Inference rules, pattern footprints, and resource boundedness
-- statement:
--   The footprint judgement has application, composition, sharing, and variable rules; the full judgement additionally has all four source weakening rules. Contexts are finite partial maps represented up to permutation. Freshness, disjoint context domains, and linearity in composition are explicit. A substitution is consistent with a context when its domain covers the context and each substituted ground value has the assigned annotation, with its typing cost existentially quantified. The potential freed by a pattern is specified by an explicit linearisation, footprint derivations for its arguments, and summation of annotations for copies of each original variable. A rule is resource bounded when the right-hand side is derivable within the root cost plus freed potential, less its charge. The budget is expressed by an equality with a nonnegative residual cost, avoiding truncated subtraction. Strict rules cost one and weak rules zero; the optional cost-free mode charges neither. Resource boundedness is syntactic and contains no assumption about operational potential decrease.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Section 5, pp. 8–10, Figure 4 and Definitions 4–6.

import Definitions.Def_MoserSchneckenreither_Annotations

/-!
Figure 2 and Definitions 4–6 of Moser–Schneckenreither, arXiv:1811.09071v1, pp. 9–11.
The footprint uses app, comp, share and var; full typing also admits the four weakenings.
Contexts are finite partial maps represented up to permutation. Freshness, disjointness,
and the linearity condition on comp are explicit.
-/

namespace MoserSchneckenreither

inductive Mode where
  | footprint
  | full

variable {sig : Signature} {P : Problem sig}

def flatContext {n : ℕ} (xs : Fin n → ℕ) (ps : Fin n → Annotation) : Context :=
  List.ofFn fun i ↦ (xs i, ps i)

/-- The source inference rules. No operational cost inequality is a constructor of this relation. -/
inductive Typing (F : AnnotatedSignature P) :
    Mode → Context → ℚ≥0 → Term sig → Annotation → Prop
  | app (mode : Mode) (f : Symbol sig) (a : Declaration (sig.arity f))
      (ha : F.declarations f a) (xs : Fin (sig.arity f) → ℕ)
      (hx : Function.Injective xs) :
      Typing F mode (flatContext xs a.inputs) a.cost (.app f fun i ↦ .var (xs i)) a.output
  | var (mode : Mode) (x : ℕ) (q : Annotation) :
      Typing F mode [(x, q)] 0 (.var x) q
  | comp {mode : Mode} (f : Symbol sig) (ts : Fin (sig.arity f) → Term sig)
      (xs : Fin (sig.arity f) → ℕ) (ps : Fin (sig.arity f) → Annotation)
      (Γs : Fin (sig.arity f) → Context) (ks : Fin (sig.arity f) → ℚ≥0)
      (k₀ : ℚ≥0) (q : Annotation) (hx : Function.Injective xs)
      (hfresh : ∀ i j, xs i ∉ (Γs j).keys)
      (hdisjoint : ∀ i j, i ≠ j → ∀ x ∈ (Γs i).keys, x ∉ (Γs j).keys)
      (hlinear : (Term.app f ts).Linear)
      (hhead : Typing F mode (flatContext xs ps) k₀ (.app f fun i ↦ .var (xs i)) q)
      (hargs : ∀ i, Typing F mode (Γs i) (ks i) (ts i) (ps i)) :
      Typing F mode (List.ofFn Γs).flatten (k₀ + (List.ofFn ks).sum) (.app f ts) q
  | share {mode : Mode} (Γ : Context) (x y z : ℕ) (p₁ p₂ p q : Annotation)
      (t : Term sig) (k : ℚ≥0) (hshare : Shares p p₁ p₂)
      (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
      (hx : x ∉ Γ.keys) (hy : y ∉ Γ.keys) (hz : z ∉ Γ.keys)
      (h : Typing F mode (Γ ++ [(x, p₁), (y, p₂)]) k t q) :
      Typing F mode (Γ ++ [(z, p)]) k
        (t.rename fun w ↦ if w = x ∨ w = y then z else w) q
  | perm {mode : Mode} {Γ Δ : Context} {k : ℚ≥0} {t : Term sig} {q : Annotation}
      (hperm : Γ.Perm Δ) (h : Typing F mode Γ k t q) : Typing F mode Δ k t q
  | w1 {Γ : Context} {k k' : ℚ≥0} {t : Term sig} {q : Annotation}
      (h : Typing F .full Γ k t q) (hk : k ≤ k') : Typing F .full Γ k' t q
  | w2 (Γ : Context) (x : ℕ) (p r q : Annotation) (k : ℚ≥0) (t : Term sig)
      (h : Typing F .full (Γ ++ [(x, r)]) k t q) (hr : r ≤ p) :
      Typing F .full (Γ ++ [(x, p)]) k t q
  | w3 {Γ : Context} {k : ℚ≥0} {t : Term sig} {q s : Annotation}
      (h : Typing F .full Γ k t s) (hq : q ≤ s) : Typing F .full Γ k t q
  | w4 (Γ : Context) (x : ℕ) (p q : Annotation) (k : ℚ≥0) (t : Term sig)
      (hx : x ∉ Γ.keys) (h : Typing F .full Γ k t q) :
      Typing F .full (Γ ++ [(x, p)]) k t q

/-- Compatibility of a normalised substitution with each context annotation, ignoring its cost. -/
def Consistent (F : AnnotatedSignature P) (σ : Substitution sig) (Γ : Context) : Prop :=
  Γ.Valid ∧ ∀ x q, (x, q) ∈ Γ → x ∈ σ.domain ∧
    ∃ k, Typing F .full [] k (σ.apply x) q

/-- Definition 5: linearise the argument patterns, derive their footprints, then merge renamings. -/
def Frees (F : AnnotatedSignature P) {n : ℕ} (ts : Fin n → Term sig)
    (ps : Fin n → Annotation) (Γ : Context) (ℓ : ℚ≥0) : Prop :=
  ∃ (us : Fin n → Term sig) (ρ : ℕ → ℕ) (Γs : Fin n → Context) (ks : Fin n → ℚ≥0),
    ((List.ofFn fun i ↦ (us i).vars).flatten).Nodup ∧
    (∀ i, (us i).rename ρ = ts i) ∧
    (∀ i, (Γs i).keys.Perm (us i).vars ∧ Typing F .footprint (Γs i) (ks i) (us i) (ps i)) ∧
    Γ = Context.renameMerge (List.ofFn Γs).flatten ρ ∧ ℓ = (List.ofFn ks).sum

/-- The syntactic budget condition for one rule and one annotation of its root. -/
def RuleBounded (F : AnnotatedSignature P) (r : Rule sig) (charge : ℚ≥0) : Prop :=
  ∀ a, F.declarations r.head a → ∃ Γ ℓ k,
    Frees F r.args a.inputs Γ ℓ ∧ a.cost + ℓ = charge + k ∧
    Typing F .full Γ k r.rhs a.output

/-- Definition 6, with cost-free boundedness selected by `countStrict = false`. -/
def ResourceBounded (F : AnnotatedSignature P) (countStrict : Bool := true) : Prop :=
  (∀ r ∈ P.strict, RuleBounded F r (if countStrict then 1 else 0)) ∧
  (∀ r ∈ P.weak, RuleBounded F r 0)

end MoserSchneckenreither


