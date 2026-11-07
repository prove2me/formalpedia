-- Prove2me | Definitions.Def_SamplingLLL_AtomicCSP
-- name    : SamplingLLL_AtomicCSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:16.070226+00:00
-- url     : https://prove2.me/theorems/6545fe2f-f07f-406b-bf8e-3cf3ef077afa
-- title:
--   Atomic CSP, dependency graph $H$, condition (C), digraph $H_G$, (SLL), input length
-- statement:
--   An event is atomic if $\mathrm{Bad}_a=\{X_v=\tau_a(v)\text{ for every }v\in\mathrm{vbl}(a)\}$ for a forbidden word $\tau_a$, and an atomic product-space CSP is a finite family of atomic events under an explicitly given rational product measure. The dependency graph $H$ joins $a\ne b$ when $\mathrm{vbl}(a)\cap\mathrm{vbl}(b)\ne\emptyset$. For numbers $p_a\ge\lambda(\mathrm{Bad}_a)$, an event $a$ is sampling-good if, for every set $T\ni a$ connected in $H$,
--   $$
--   \lambda\Big(\bigcap_{b\in T}\mathrm{Bad}_b\Big)\le p_a\prod_{b\in T\setminus\{a\}}2p_b. \tag{C}
--   $$
--   For a set $G$, the sampling dependency digraph $H_G$ has an arc from $a$ to $b$ when $b\in\Gamma_H(a)$, and also when $\mathrm{dist}_H(a,b)=2$ and $a\notin G$. Condition (SLL) is
--   $$
--   4p_a\le x_a\prod_{b\in\Gamma_{H_G}(a)}(1-x_b)\qquad(a\in A).
--   $$
--   The input length $L$ counts the variables, the constraints, the bits of the law, the forbidden words, the bits of the witnesses $x_a$, and the bitmap of $G$.
--
--   **Formalization Note** The forbidden word is a partial function on variables, so a scope has no repeated variable; empty scopes and identical constraints are allowed by the structure. Condition (C) ranges over all connected $T\ni a$, compatible or not.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Definition 2.1 and Definition 2.2, p.7; Definition 2.5 and Theorem 2.6, p.8

import Mathlib
import Definitions.Def_SamplingLLL_ProductCSP

set_option autoImplicit false

namespace SamplingLLL

/-- Bit length `Nat.size |a| + Nat.size b` of a rational `a/b` in lowest terms (the encoding used
for every rational of the input and for every charge of a rational operation). -/
def bits (q : ℚ) : ℕ := q.num.natAbs.size + q.den.size

/-- Definition 2.1, p.7: an atomic product-space CSP, a finite family of atomic events under an
explicitly given rational product measure. `word a v = some w` says `v ∈ vbl(a)` and `τ_a(v) = w`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Definition 2.1, p.7.

**Formalization Note.** The forbidden word is a partial function on the variables, so a scope has
no repeated variable. Empty scopes and identical constraints are allowed by the structure. -/
structure AtomicCSP (n m : ℕ) where
  /-- `Ω_v = Fin (dom v + 1)`. -/
  dom : Fin n → ℕ
  /-- The coordinate law `λ_v`. -/
  lam : (v : Fin n) → Fin (dom v + 1) → ℚ
  lam_nonneg : ∀ v w, 0 ≤ lam v w
  lam_sum : ∀ v, ∑ w, lam v w = 1
  /-- The forbidden word `τ_a` on the scope `vbl(a)`. -/
  word : Fin m → (v : Fin n) → Option (Fin (dom v + 1))

namespace AtomicCSP

variable {n m : ℕ} (I : AtomicCSP n m)

/-- The scope `vbl(a)`. -/
def vbl (a : Fin m) : Finset (Fin n) := Finset.univ.filter fun v => (I.word a v).isSome

/-- `Bad_a = {X_v = τ_a(v) for every v ∈ vbl(a)}`, Definition 2.1. -/
def bad (a : Fin m) (x : (v : Fin n) → Fin (I.dom v + 1)) : Bool :=
  decide (∀ v, ∀ w, I.word a v = some w → x v = w)

/-- The underlying product-space CSP. -/
abbrev toCSP : ProductCSP n m where
  dom := I.dom
  lam := I.lam
  lam_nonneg := I.lam_nonneg
  lam_sum := I.lam_sum
  vbl := I.vbl
  bad := I.bad
  bad_dep := by
    intro a x y h
    have key : (∀ v, ∀ w, I.word a v = some w → x v = w) ↔
        (∀ v, ∀ w, I.word a v = some w → y v = w) := by
      constructor
      · intro hx v w hw
        have hv : v ∈ I.vbl a := by simp [vbl, hw]
        rw [← h v hv]; exact hx v w hw
      · intro hy v w hw
        have hv : v ∈ I.vbl a := by simp [vbl, hw]
        rw [h v hv]; exact hy v w hw
    simp only [bad, key]

/-- Definition 2.2, p.7: the dependency graph `H` on `A`, joining `a` and `b` when
`vbl(a) ∩ vbl(b) ≠ ∅`. -/
def H : SimpleGraph (Fin m) where
  Adj a b := a ≠ b ∧ ∃ v, (I.word a v).isSome ∧ (I.word b v).isSome
  symm := ⟨fun a b h => by
    obtain ⟨hne, v, h1, h2⟩ := h
    exact ⟨hne.symm, v, h2, h1⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance : DecidableRel I.H.Adj := fun a b => by
  unfold H; exact inferInstanceAs (Decidable (a ≠ b ∧ ∃ v, (I.word a v).isSome ∧ (I.word b v).isSome))

/-- `dist_H(a,b) = 2`, written out: distinct, not adjacent, with a common neighbour. Equivalent
to `I.H.dist a b = 2` (`Solutions/verification/SamplingLLL_Sanity.lean`). -/
def DistTwo (a b : Fin m) : Prop := a ≠ b ∧ ¬ I.H.Adj a b ∧ ∃ e, I.H.Adj a e ∧ I.H.Adj e b

instance (a b : Fin m) : Decidable (I.DistTwo a b) := by unfold DistTwo; infer_instance

/-- Definition 2.5, p.8: `Γ_{H_G}(a)`, the out-neighbours of `a` in the sampling dependency digraph:
an arc to `b` when `b ∈ Γ_H(a)`, and also when `dist_H(a,b) = 2` and `a ∉ G`. -/
def gammaG (G : Finset (Fin m)) (a : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun b => I.H.Adj a b ∨ (I.DistTwo a b ∧ a ∉ G)

/-- `λ(⋂_{b∈T} Bad_b)`. -/
def jointBad (T : Finset (Fin m)) : ℚ :=
  I.toCSP.prob fun x => decide (∀ b ∈ T, I.toCSP.bad b x = true)

/-- `λ(Bad_a)`. -/
def badProb (a : Fin m) : ℚ := I.toCSP.prob (I.toCSP.bad a)

/-- Definition 2.5, p.8, condition (C): `a` is sampling-good for the numbers `p` when
`λ(⋂_{b∈T} Bad_b) ≤ p_a ∏_{b∈T∖{a}} 2p_b` for every `T ∋ a` connected in `H`.

**Formalization Note.** `T` ranges over all `H`-connected sets containing `a`, compatible or not. -/
def SamplingGood (p : Fin m → ℝ) (a : Fin m) : Prop :=
  ∀ T : Finset (Fin m), a ∈ T → (I.H.induce (T : Set (Fin m))).Connected →
    ((I.jointBad T : ℚ) : ℝ) ≤ p a * ∏ b ∈ T.erase a, (2 * p b)

/-- Theorem 2.6, p.8, condition (SLL): `4 p_a ≤ x_a ∏_{b∈Γ_{H_G}(a)} (1 - x_b)` for every `a`. -/
def SLL (G : Finset (Fin m)) (p : Fin m → ℝ) (x : Fin m → ℚ) : Prop :=
  ∀ a, 4 * p a ≤ (x a : ℝ) * ∏ b ∈ I.gammaG G a, (1 - (x b : ℝ))

/-- The input length `L` of an instance with its witnesses and the bitmap of `G` (Theorem 2.6, p.8:
"the input length, including the binary encodings of the witnesses"):
`n + m + Σ_v Σ_w bits(λ_v(w)) + Σ_a Σ_{v∈vbl(a)} (1 + size v + size τ_a(v)) + Σ_a bits(x_a) + m`. -/
def inputSize (x : Fin m → ℚ) : ℕ :=
  n + m + (∑ v, ∑ w, bits (I.lam v w)) +
    (∑ a, ∑ v, match I.word a v with
      | some w => 1 + (v : ℕ).size + (w : ℕ).size
      | none => 0) +
    (∑ a, bits (x a)) + m

end AtomicCSP

end SamplingLLL


