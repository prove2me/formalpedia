-- Prove2me | Definitions.Def_LatticePrepro_PCP_Verifier
-- name    : LatticePrepro_PCP_Verifier
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:09:09.256902+00:00
-- url     : https://prove2.me/theorems/568b651c-aa6d-44b7-8317-d9b25556be8d
-- title:
--   Query-oblivious PCPs with enumerable predicate families, and their accepting views (Definition 6.1)
-- statement:
--   These definitions formalize the query-oblivious PCP verifiers used in the reduction of Section 6.
--
--   1. **Query-oblivious PCP** (`ObliviousPCP X`). For a set $X$ of instances: a finite alphabet $\Sigma$, a proof length $\ell$, a number $\mathsf R$ of random bits, a number $\mathsf q\ge1$ of queries, and
--      - for every random string $r\in\{0,1\}^{\mathsf R}$, a query tuple $I_r=(u_{r,1},\dots,u_{r,\mathsf q})\in[\ell]^{\mathsf q}$;
--      - for every $r$, a finite family $\mathcal D_r$ of labeled predicates $\Sigma^{\mathsf q}\to\{0,1\}$, given by a finite set of labels and an evaluation map (different labels may give the same function);
--      - for every instance $x\in X$ and every $r$, the label in $\mathcal D_r$ of the acceptance predicate $V_{x,r}$.
--
--      Neither $I_r$ nor $\mathcal D_r$ depends on the instance.
--   2. **Acceptance** (`Accepts`). The verifier accepts a proof $\pi\in\Sigma^{\ell}$ on the instance $x$ and the random string $r$ if $V_{x,r}(\pi|_{I_r})=1$, where $\pi|_{I_r}=(\pi(u_{r,1}),\dots,\pi(u_{r,\mathsf q}))$.
--   3. **Perfect completeness** (`PerfectlyComplete`) for a language $L\subseteq X$: every $x\in L$ has a proof that is accepted for every random string.
--   4. **Soundness error** (`SoundnessError`) $\mathsf s$ for $L$, with $\mathsf s$ a real number: for every $x\notin L$ and every proof $\pi$, the number of random strings for which $\pi$ is accepted is at most $\mathsf s\cdot2^{\mathsf R}$. That is, every proof is accepted with probability at most $\mathsf s$.
--   5. **Accepting views** (`View`, `Views`). An accepting view for $r$ is a pair $(V,\mathbf a)\in\mathcal D_r\times\Sigma^{\mathsf q}$ with $V(\mathbf a)=1$ and $a_j=a_{j'}$ whenever $u_{r,j}=u_{r,j'}$; the last condition says that $\mathbf a=\pi|_{I_r}$ for some proof $\pi$. The set of accepting views for $r$ is $\mathcal V_r$, and `Views` is the disjoint union of the sets $\mathcal V_r$, of size $\mathsf m=\sum_r|\mathcal V_r|$. `View.pred` and `View.ans` are the two components $V$ and $\mathbf a$ of a view.
--
--   This is Definition 6.1 of the paper. The accepting-view code of Construction 6.2 and the reduction of Theorem 6.4 are stated for these objects.
--
--   **Formalization Note.** Instances form an arbitrary type $X$ (the paper takes $X=\{0,1\}^{n}$), and $L$ is an arbitrary subset of $X$ rather than the language of a relation. Random strings are functions `Fin ρ → Bool`, proof locations are elements of `Fin ℓ`, and queries are indexed by `Fin q`. The Lean field names `ρ` and `q` stand for $\mathsf R$ and $\mathsf q$, and the theorems call the soundness error `ε`. Predicates take values in `Bool`, and equality of predicates is equality of labels, as in the paper. The running times of the verifier and of the predicate enumerator (the parameter $\mathsf{vt}$) are not formalized.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Definition 6.1 (\label{def:query-oblivious-pcp}); Lean: LatticePrepro/PCP/Verifier.lean, LatticePrepro.ObliviousPCP, LatticePrepro.ObliviousPCP.Rand, LatticePrepro.ObliviousPCP.Proof, LatticePrepro.ObliviousPCP.Accepts, LatticePrepro.ObliviousPCP.PerfectlyComplete, LatticePrepro.ObliviousPCP.SoundnessError, LatticePrepro.ObliviousPCP.View, LatticePrepro.ObliviousPCP.View.pred, LatticePrepro.ObliviousPCP.View.ans, LatticePrepro.ObliviousPCP.Views

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

/-!
# Query-oblivious PCPs (Definition 6.1)

A query-oblivious PCP verifier reads `q ≥ 1` locations of a proof `π ∈ Σ^ℓ`, chosen by a random
string `r ∈ {0,1}^ρ` alone, and applies an acceptance predicate `V_{x,r} : Σ^q → {0,1}` that may
depend on the instance `x`. For the reduction of Section 6 the predicates that can occur for a
random string `r` are listed as a family `𝒟_r` of *labeled* predicates, which does not depend on
`x`.

* `ObliviousPCP X` is this data, for instances in an arbitrary type `X` (the paper takes
  `X = {0,1}^n`). The query tuple `I_r` (`query`) and the families `𝒟_r` (`Pred`, `eval`) do not
  take the instance as an argument; the verifier (`verifier`) returns the label of `V_{x,r}`.
* `PerfectlyComplete Lang` and `SoundnessError Lang ε` are perfect completeness and soundness
  error `ε` with respect to a language `Lang ⊆ X`.
* `View r` is the set `𝒱_r` of accepting views for `r`, and `Views` is the set of all accepting
  views; `card_views_le` is the bound `m ≤ 2^ρ · K · |Σ|^q` on their number `m`.

Notation: the symbols follow the paper, except that the number of random bits is `ρ` (the
paper's `𝖱`) and the soundness error is `ε` (the paper's `𝗌`). The bound `K` on the number of
predicates per random string is the paper's `𝗸`.

The running times of the verifier and of the predicate enumerator are not formalized.
-/

namespace LatticePrepro

/-- A query-oblivious PCP verifier with enumerable predicate families (Definition 6.1), for
instances in `X`. -/
structure ObliviousPCP (X : Type) where
  /-- The alphabet `Σ`. -/
  Alphabet : Type
  [fintypeAlphabet : Fintype Alphabet]
  [decEqAlphabet : DecidableEq Alphabet]
  /-- The proof length `ℓ`. -/
  ℓ : ℕ
  /-- The number `ρ` of random bits. -/
  ρ : ℕ
  /-- The number `q` of queries. -/
  q : ℕ
  /-- The verifier makes at least one query. -/
  q_pos : 0 < q
  /-- The query tuple `I_r = (u_{r,1}, …, u_{r,q})`. It does not depend on the instance. -/
  query : (Fin ρ → Bool) → Fin q → Fin ℓ
  /-- The labels of the predicate family `𝒟_r`. It does not depend on the instance. -/
  Pred : (Fin ρ → Bool) → Type
  [fintypePred : ∀ r, Fintype (Pred r)]
  [decEqPred : ∀ r, DecidableEq (Pred r)]
  /-- The predicate `Σ^q → {0,1}` with a given label. Different labels may give the same
  function. -/
  eval : (r : Fin ρ → Bool) → Pred r → (Fin q → Alphabet) → Bool
  /-- The label in `𝒟_r` of the acceptance predicate `V_{x,r}`. -/
  verifier : X → (r : Fin ρ → Bool) → Pred r

namespace ObliviousPCP

attribute [instance] fintypeAlphabet decEqAlphabet fintypePred decEqPred

variable {X : Type} (P : ObliviousPCP X)

/-- Random strings `r ∈ {0,1}^ρ`. -/
abbrev Rand : Type := Fin P.ρ → Bool

/-- Proofs `π ∈ Σ^ℓ`. -/
abbrev Proof : Type := Fin P.ℓ → P.Alphabet

/-- The verifier accepts the proof `π` on instance `x` and random string `r`:
`V_{x,r}(π|_{I_r}) = 1`. -/
def Accepts (x : X) (r : P.Rand) (π : P.Proof) : Prop :=
  P.eval r (P.verifier x r) (fun j => π (P.query r j)) = true

instance (x : X) (r : P.Rand) (π : P.Proof) : Decidable (P.Accepts x r π) :=
  inferInstanceAs (Decidable (P.eval r (P.verifier x r) (fun j => π (P.query r j)) = true))

/-- Perfect completeness: every instance in `Lang` has a proof that is accepted for every random
string. -/
def PerfectlyComplete (Lang : Set X) : Prop :=
  ∀ x ∈ Lang, ∃ π : P.Proof, ∀ r, P.Accepts x r π

/-- Soundness error `ε`: for an instance outside `Lang`, every proof is accepted for at most an
`ε` fraction of the `2^ρ` random strings. -/
def SoundnessError (Lang : Set X) (ε : ℝ) : Prop :=
  ∀ x, x ∉ Lang → ∀ π : P.Proof,
    ((Finset.univ.filter fun r => P.Accepts x r π).card : ℝ) ≤ ε * 2 ^ P.ρ

/-- The accepting views `𝒱_r` for the random string `r`: pairs `(V, a)` of a labeled predicate
`V ∈ 𝒟_r` and an answer tuple `a ∈ Σ^q` with `V(a) = 1` and `a = π|_{I_r}` for some proof `π`,
that is, `a_j = a_{j'}` whenever `u_{r,j} = u_{r,j'}`. -/
abbrev View (r : P.Rand) : Type :=
  {p : P.Pred r × (Fin P.q → P.Alphabet) //
    P.eval r p.1 p.2 = true ∧ ∀ j j', P.query r j = P.query r j' → p.2 j = p.2 j'}

variable {P} in
/-- The labeled predicate of an accepting view. -/
def View.pred {r : P.Rand} (w : P.View r) : P.Pred r := w.1.1

variable {P} in
/-- The answer tuple of an accepting view. -/
def View.ans {r : P.Rand} (w : P.View r) : Fin P.q → P.Alphabet := w.1.2

/-- All accepting views, over all random strings. Their number is `m`. -/
abbrev Views : Type := Σ r : P.Rand, P.View r

end ObliviousPCP

end LatticePrepro


