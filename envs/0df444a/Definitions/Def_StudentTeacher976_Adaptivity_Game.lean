-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_Game
-- name    : StudentTeacher976_Adaptivity_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:56.905613+00:00
-- url     : https://prove2.me/theorems/e88bcc47-93e3-4967-8c7c-c9af317f0d06
-- title:
--   Causal simultaneous-query Student–Teacher games (Definition 1.2)
-- statement:
--   Fix a hierarchy level $i$, a total refutable search relation $R$, and its predicate $\varphi$ with refutation-length polynomial $b$. At input $x$ of length $n$, a uniform student in $\mathrm{FP}^{\Sigma_i^p}$ receives the round number and all earlier reply batches. In each of $r(n)$ rounds it outputs exactly $q(n)$ polynomially bounded candidate answers simultaneously, before receiving that round's replies. It rejects after the budget.
--
--   For every complete history $H=(H_0,\ldots,H_{r(n)-1})$ with $q(n)$ refutations of length $b(n)$ per batch, success means
--
--   $$
--   \exists t<r(n)\;\exists j<q(n):
--   \varphi\bigl(x,f(x,t,H_{<t})_j,(H_t)_j\bigr).
--   $$
--
--   All histories are quantified, including replies that are not valid refutations. The teacher has no computational bound. Class membership $R\in\mathrm{ST}^{\Sigma_i^p}[r,q]$ means that some faithful presentation of this same $R$ and some uniform student satisfy this condition.
--
--   This definition isolates the causal timing that makes the exact round separation meaningful. Internal rounds are zero based, encoded rounds are one based, and the explicit empty-input resource convention is inherited from the complexity layer.
-- source:
--   Ondřej Ježil, Dimitrios Tsintsilidas, STOC 2027 submission #976 (October 2026), Definition 1.2, p.7 (PDF p.7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Refutable

open QAdvFew.PoQOracle

namespace StudentTeacher976.Adaptivity

/-- A batch is simultaneous. A student receives only preceding batches. Internal round
t is zero based; the encoded round is t+1, matching Definition 1.2, p.7. -/
abbrev Student := Word → ℕ → List (List Word) → List Word

/-- Uniform realization of the student on self-delimiting structured inputs. The machine
halts on every bit string (InFP); malformed inputs therefore do not constitute a promise. -/
def UniformStudent (i : ℕ) (f : Student) : Prop :=
  ∃ F : Word → Word, InFP i F ∧ ∀ x t H,
    F (tup [x, List.replicate (t + 1) true, tup (H.map tup)]) = tup (f x t H)

/-- Exactly h prior rounds, each having q refutations of exactly w bits. -/
def HistoryShape (h q w : ℕ) (H : List (List Word)) : Prop :=
  H.length = h ∧ ∀ B ∈ H, B.length = q ∧ ∀ z ∈ B, z.length = w

/-- Well-formed students output exactly q candidates, bounded by one polynomial in the
original input length on legal histories; beyond the budget they reject with an empty batch. -/
def StudentShape {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
    (r q : ℕ → ℕ) (f : Student) : Prop :=
  (∃ b : Polynomial ℕ, ∀ x t H, t < resource r x.length →
    HistoryShape t (resource q x.length) (P.refutationLength.eval x.length) H →
    (f x t H).length = resource q x.length ∧
      ∀ y ∈ f x t H, y.length ≤ b.eval x.length) ∧
  ∀ x t H, resource r x.length ≤ t → f x t H = []

/-- The universal-history disjunction in Definition 1.2, p.7, with every t and j in
range. H.take t is the sole teacher input to round t: the current H[t] is unavailable.
Arbitrary histories, not only valid counterexamples, are universally quantified. -/
def StudentWins {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
    (r q : ℕ → ℕ) (f : Student) : Prop :=
  ∀ x H, HistoryShape (resource r x.length) (resource q x.length)
    (P.refutationLength.eval x.length) H →
    ∃ t, t < resource r x.length ∧ ∃ j, j < resource q x.length ∧
      P.test x ((f x t (H.take t)).getD j []) ((H.getD t []).getD j [])

/-- Definition 1.2, p.7. Membership is membership of the underlying relation, through
one faithful presentation and one uniform student, with no computational bound on the teacher. -/
def ST (i : ℕ) (r q : ℕ → ℕ) : Set SearchRelation :=
  {R | ∃ P : RefutablePresentation i R, ∃ f : Student,
    UniformStudent i f ∧ StudentShape P r q f ∧ StudentWins P r q f}

end StudentTeacher976.Adaptivity


