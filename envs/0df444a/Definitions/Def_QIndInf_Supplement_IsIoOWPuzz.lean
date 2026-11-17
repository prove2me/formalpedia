-- Prove2me | Definitions.Def_QIndInf_Supplement_IsIoOWPuzz
-- name    : QIndInf_Supplement_IsIoOWPuzz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:22:48.075906+00:00
-- url     : https://prove2.me/theorems/911dd2f1-3071-45ce-880d-f1088daecf07
-- title:
--   Definition 3.7 — infinitely-often one-way puzzles
-- statement:
--   An **infinitely-often one-way puzzle** over a gate set $G$ is a pair $(\mathsf{Samp},\mathsf{Ver})$ where $\mathsf{Samp}$ is a QPT algorithm that on $1^\lambda$ outputs a pair $(\mathsf{puzz},\mathsf{ans})$ of classical strings, and $\mathsf{Ver}$ is an arbitrary (computationally unbounded) map $(\mathsf{puzz},\mathsf{ans}')\mapsto\top/\bot$, such that
--
--   1. (correctness) for a negligible function $\nu$ and all $\lambda$,
--   $$\Pr\big[\top\leftarrow\mathsf{Ver}(\mathsf{puzz},\mathsf{ans}):(\mathsf{puzz},\mathsf{ans})\leftarrow\mathsf{Samp}(1^\lambda)\big]\ \ge\ 1-\nu(\lambda);$$
--   2. (security) for every QPT adversary $\mathcal A$ and every polynomial $p$,
--   $$\Pr\big[\top\leftarrow\mathsf{Ver}(\mathsf{puzz},\mathcal A(1^\lambda,\mathsf{puzz})):(\mathsf{puzz},\mathsf{ans})\leftarrow\mathsf{Samp}(1^\lambda)\big]\ \le\ \frac1{p(\lambda)}$$
--   for infinitely many $\lambda$.
--
--   Infinitely-often one-way puzzles **exist** if some such pair exists. This is the cryptographic assumption of Theorems 4.4 and 5.5.
--
--   **Formalization Note** An output of $\mathsf{Samp}$ that is not a pair counts as rejected. Negligible functions are the published `QAdvFew.PoQOracle.Negligible`; polynomials are `Polynomial ℕ` with values at least $1$.
-- source:
--   Hiroka, Hsieh, Shirakawa, Universal Inductive Inference of Quantum States, arXiv:2609.36912 (PDF of 2026-11-02, sha256 ac6387756651cc50c671f36acf1ef987db0df0c463581cd948250204441f6925), §3.4, Definition 3.7, Eqs. (47)–(48), p.17

import Mathlib
import Definitions.Def_QIndInf_Supplement_IsQPT
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QAdvFew_PoQOracle_Negligible

set_option autoImplicit false

namespace QIndInf.Supplement

open QAlgorithms.Complexity QiOPoQ

/-- The value `[Ver(puzz, ans) = ⊤]` on an output `z` of `Samp`, which must be a pair
`(puzz, ans)`; an output that is not a pair counts as rejected. -/
noncomputable def verPair (Ver : List Bool → List Bool → Bool) (z : List Bool) : ℝ :=
  match untuple z with
  | some [puzz, ans] => if Ver puzz ans then 1 else 0
  | _ => 0

/-- Correctness probability `Pr[⊤ ← Ver(puzz, ans) : (puzz, ans) ← Samp(1^λ)]` (Eq. (47)). -/
noncomputable def owCorrect (G : GateSet) (Samp : List Bool) (Ver : List Bool → List Bool → Bool)
    (lam : ℕ) : ℝ :=
  ∑' z : List Bool, algProb G Samp (unary lam) z * verPair Ver z

/-- Inversion probability `Pr[⊤ ← Ver(puzz, A(1^λ, puzz)) : (puzz, ans) ← Samp(1^λ)]`
(Eq. (48)); `A` is run on the pair `(1^λ, puzz)`. -/
noncomputable def owBreak (G : GateSet) (Samp : List Bool) (Ver : List Bool → List Bool → Bool)
    (A : List Bool) (lam : ℕ) : ℝ :=
  ∑' z : List Bool, algProb G Samp (unary lam) z *
    (match untuple z with
      | some [puzz, _] => ∑' w : List Bool, algProb G A (pair (unary lam) puzz) w *
          (if Ver puzz w then 1 else 0)
      | _ => 0)

/-- **Infinitely-often one-way puzzle** (Definition 3.7 [KT24]). `(Samp, Ver)` with `Samp` a QPT
algorithm that on `1^λ` outputs a pair `(puzz, ans)` of classical strings and `Ver` an unbounded
(arbitrary) map `(puzz, ans′) ↦ ⊤/⊥`, such that
* (correctness) `Pr[⊤ ← Ver(puzz, ans)] ≥ 1 − negl(λ)` for all `λ`;
* (security) for every QPT adversary `A` and every polynomial `p`,
  `Pr[⊤ ← Ver(puzz, A(1^λ, puzz))] ≤ 1/p(λ)` for infinitely many `λ`.

arXiv:2609.36912 (PDF of 2026-11-02), §3.4, Definition 3.7, Eqs. (47)–(48), p.17.

**Formalization Note.** QPT is `IsQPT` over the gate set `G`; `negl` is the published
`QAdvFew.PoQOracle.Negligible`; "infinitely many `λ`" is `∃ᶠ λ in atTop`. Polynomials are
`Polynomial ℕ` with values `≥ 1` (so that `1/p(λ)` is the paper's inverse polynomial). -/
def IsIoOWPuzz (G : GateSet) (Samp : List Bool) (Ver : List Bool → List Bool → Bool) : Prop :=
  IsQPT Samp ∧
    (∃ ν : ℕ → ℝ, QAdvFew.PoQOracle.Negligible ν ∧ ∀ lam, 1 - ν lam ≤ owCorrect G Samp Ver lam) ∧
    ∀ A : List Bool, IsQPT A → ∀ p : Polynomial ℕ, (∀ lam, 1 ≤ p.eval lam) →
      ∃ᶠ lam in Filter.atTop, owBreak G Samp Ver A lam ≤ 1 / ((p.eval lam : ℕ) : ℝ)

/-- Infinitely-often one-way puzzles exist (over the gate set `G`). -/
def IoOWPuzzExists (G : GateSet) : Prop :=
  ∃ (Samp : List Bool) (Ver : List Bool → List Bool → Bool), IsIoOWPuzz G Samp Ver

end QIndInf.Supplement


