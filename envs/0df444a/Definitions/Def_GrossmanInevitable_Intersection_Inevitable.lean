-- Prove2me | Definitions.Def_GrossmanInevitable_Intersection_Inevitable
-- name    : GrossmanInevitable_Intersection_Inevitable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:05:36.69399+00:00
-- url     : https://prove2.me/theorems/ad2c5b2b-ac71-4b1a-92be-16e9f88e6a3f
-- title:
--   $\alpha$-inevitable and $\alpha$-R-inevitable (Definitions 1.2, 3.1) and the relation $R_g$ of a function (Definition 3.2)
-- statement:
--   Let $A$ and $B$ be finite input domains. Let $f:A\times B\to C$, let $R\subseteq A\times B\times W$ be a relation, and let $\alpha:A\times B\to[0,\infty]$.
--
--   **Definition 3.1.** $R$ is **$\alpha$-inevitable** for $f$ (`IsInevitable f R α`) if the following holds. For every deterministic protocol $\pi_f$ computing $f$, i.e. with $\mathrm{val}(\pi_f(a,b))=f(a,b)$ for all $(a,b)$, there is a deterministic protocol with advice $\pi_R$ such that for every $(a,b)$ with $\alpha(a,b)<\infty$:
--
--   - $w=\mathrm{val}(\pi_R(a,b,\pi_f(a,b)))$ is an $R$-witness of $(a,b)$ if one exists and $\bot$ otherwise;
--   - $|\pi_R(a,b,\pi_f(a,b))|\le\alpha(a,b)$.
--
--   Here $\pi_R$ is a family of protocols indexed by the advice string, and it receives the transcript $\pi_f(a,b)$ as advice. Only its own bits are counted. Inputs with $\alpha(a,b)=\infty$ impose no requirement.
--
--   $R$ is **$\alpha$-R-inevitable** for $f$ (`IsRInevitable`) if the same holds with $\pi_R$ a Las Vegas protocol with advice. On every $(a,b)$ with $\alpha(a,b)<\infty$ and advice $\pi_f(a,b)$, it must have zero error, and its expected communication must be at most $\alpha(a,b)$.
--
--   **Definition 1.2** is the Boolean case. For $f:A\times B\to\{0,1\}$ and a constant $\alpha$, `IsInevitableBool f R α` and `IsRInevitableBool f R α` take $\alpha(a,b)=\alpha$ on $f^{-1}(1)$ and $\alpha(a,b)=\infty$ on $f^{-1}(0)$, as the paper notes on p. 17.
--
--   **Definition 3.2.** For $g:A\times B\to W$, $R_g=\{(a,b,g(a,b))\}$ (`graphRel g`). "Computing $g$ is $\alpha$-inevitable for $f$" means that $R_g$ is $\alpha$-inevitable for $f$.
--
--   Formalization note: the source takes $\alpha$ with values in $\mathbb N\cup\{\infty\}$. Here $\alpha$ takes values in $[0,\infty]$, which contains these values and gives them the same meaning: a bit count is $\le\alpha$ iff it is $\le\lfloor\alpha\rfloor$. $\pi_R$ may depend on $\pi_f$, and $\pi_f$ ranges over all deterministic protocols computing $f$, of any cost.
-- source:
--   Grossman, Grossman, Naor, Shulman, Inevitable Knowledge in Communication Complexity and the LOCAL Model, STOC 2027 submission (manuscript sha256 67c87783…), Definition 1.2 pp. 2–3 (PDF 4–5); Definitions 3.1 and 3.2, p. 17 (PDF 19)

import Mathlib
import Definitions.Def_OneOfManyCC_Protocol
import Definitions.Def_GrossmanInevitable_Intersection_Transcript
import Definitions.Def_GrossmanInevitable_Intersection_Relation
import Definitions.Def_GrossmanInevitable_Intersection_LasVegas

namespace GrossmanInevitable.Intersection

open OneOfManyCC

/-- **`α`-inevitable** (Definition 3.1, printed p. 17 / PDF 19). `f : A → B → C`, a relation
`R ⊆ A × B × W` and `α : A × B → [0, ∞]`, with finite input domains as in §2. For every deterministic protocol `πf` computing `f`
(`val(πf(a, b)) = f(a, b)` for every `(a, b)`) there is a deterministic protocol with advice `πR`
(a family of protocols indexed by the advice string `σ`) such that for every input `(a, b)` with
`α(a, b) < ∞`, run with the advice `σ = πf(a, b)` (the transcript of `πf`), its output
`w = val(πR(a, b, πf(a, b)))` is an `R`-witness of `(a, b)` if `(a, b)` has one and `⊥` otherwise,
and `|πR(a, b, πf(a, b))| ≤ α(a, b)`. Inputs with `α(a, b) = ∞` impose no requirement.

The source takes `α` with values in `ℕ ∪ {∞}`; here `α` takes values in `[0, ∞]`, which contains
it and means the same on it (a cost in `ℕ` is `≤ α` iff it is `≤ ⌊α⌋`). -/
def IsInevitable {A B C W : Type} [Finite A] [Finite B] (f : A → B → C) (R : A → B → W → Prop)
    (α : A → B → ENNReal) : Prop :=
  ∀ πf : Protocol A B C, (∀ a b, πf.eval a b = f a b) →
    ∃ πR : List Bool → Protocol A B (Option W), ∀ a b, α a b ≠ ⊤ →
      CorrectOut R a b ((πR (transcript πf a b)).eval a b) ∧
      ((cost (πR (transcript πf a b)) a b : ℕ) : ENNReal) ≤ α a b

/-- **`α`-R-inevitable** (Definition 3.1, printed p. 17 / PDF 19): as `IsInevitable`, but `πR` is a
zero-error protocol using private randomness (`LVProtocol`): for every deterministic protocol `πf`
computing `f` there is a Las Vegas protocol with advice `πR` such that on every input `(a, b)` with
`α(a, b) < ∞`, given the advice `πf(a, b)`, it stops with probability 1 with a correct output
(`ZeroErrorOn`) and its expected communication is at most `α(a, b)`. -/
def IsRInevitable {A B C W : Type} [Finite A] [Finite B] (f : A → B → C) (R : A → B → W → Prop)
    (α : A → B → ENNReal) : Prop :=
  ∀ πf : Protocol A B C, (∀ a b, πf.eval a b = f a b) →
    ∃ πR : LVProtocol A B (Option W), ∀ a b, α a b ≠ ⊤ →
      πR.ZeroErrorOn R (transcript πf a b) a b ∧ πR.expCost (transcript πf a b) a b ≤ α a b

/-- **`α`-inevitable for a decision problem** (Definition 1.2, printed pp. 2–3 / PDF 4–5), for
`f : A → B → Bool` (`true` = 1) and a constant `α`: the special case of Definition 3.1 with
`α(a, b) = α` on `f⁻¹(1)` and `α(a, b) = ∞` on `f⁻¹(0)` (printed p. 17 / PDF 19). On `f⁻¹(1)`, where
Definition 1.2 assumes a witness exists, a correct output is a witness. -/
def IsInevitableBool {A B W : Type} [Finite A] [Finite B] (f : A → B → Bool) (R : A → B → W → Prop) (α : ENNReal) :
    Prop :=
  IsInevitable f R (fun a b => if f a b = true then α else ⊤)

/-- **`α`-R-inevitable for a decision problem** (Definition 1.2, printed p. 3 / PDF 5): a
zero-error private-randomness `πR` with expected communication at most `α` on every input in
`f⁻¹(1)`; the special case of `IsRInevitable` with `α` on `f⁻¹(1)` and `∞` on `f⁻¹(0)`. -/
def IsRInevitableBool {A B W : Type} [Finite A] [Finite B] (f : A → B → Bool) (R : A → B → W → Prop) (α : ENNReal) :
    Prop :=
  IsRInevitable f R (fun a b => if f a b = true then α else ⊤)

/-- The relation `R_g = {(a, b, g(a, b)) : (a, b) ∈ A × B}` of a function `g : A × B → W`
(Definition 3.2, printed p. 17 / PDF 19). "`g` is `α`-inevitable for `f`", or "computing `g` is
`α`-inevitable for `f`", means that `graphRel g` is `α`-inevitable for `f`. -/
def graphRel {A B W : Type} (g : A → B → W) : A → B → W → Prop :=
  fun a b w => w = g a b

end GrossmanInevitable.Intersection


