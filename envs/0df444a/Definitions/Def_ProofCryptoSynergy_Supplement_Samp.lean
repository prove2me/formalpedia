-- Prove2me | Definitions.Def_ProofCryptoSynergy_Supplement_Samp
-- name    : ProofCryptoSynergy_Supplement_Samp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:45:20.110021+00:00
-- url     : https://prove2.me/theorems/7971d093-11df-4adc-a824-b0c29a89393f
-- title:
--   Sampling circuits, their support, agreement probability, and the function they define
-- statement:
--   A **sampling circuit** $E$ is a multi-output Boolean circuit on $m$ uniformly random coin bits with $n+1$ outputs; on coins $r$ it outputs a labelled example $E(r)=(x,b)\in\{0,1\}^n\times\{0,1\}$. Its **support** $\mathrm{supp}(E)$ is the set of pairs it outputs, and for a circuit $C$ with $n$ inputs
--   $$\Pr_{(x,b)\sim E}[C(x)=b]=2^{-m}\,\#\{r\in\{0,1\}^m: C(x_r)=b_r\}.$$
--
--   $E$ **defines a (partial) boolean function** if no $x$ has both $(x,0)$ and $(x,1)$ in its support (Definition 24); its first coordinate $X$ has **full support** if every $x\in\{0,1\}^n$ occurs (Definition 23).
--
--   These are the instances of the learning problems CGL, Total-Learn, Gap-ImpMCSP, Gap-ImpMCSP∗ and Extension-Learn.
--
--   **Formalization Note** Circuits are the published `LaconicBarrier.MCircuit` (samplers) and `KarpLiptonOM.Circuit` (learners, size = number of gates). "poly(n)-size" names no polynomial, so the type carries no size bound; the theorems require every sampler a reduction outputs to have description length polynomial in its input length (`PolySizeOut`).
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definitions 21, 23, 24, pp.22–23 (PDF 24–25)

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_LaconicBarrier_coinAvg

open KarpLiptonOM LaconicBarrier

namespace ProofCryptoSynergy.Supplement

/-- A **sampling circuit** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 21, p.22 (PDF 24): "a poly(n)-size circuit `E`
sampling a joint distribution supported over `{0,1}ⁿ × {0,1}`"): a multi-output circuit `E.2`
(published `LaconicBarrier.MCircuit`) on `E.1` coin bits. Its last output is the label `b`, the
others are the example `x`.

**Formalization Note** "poly(n)-size" names no polynomial, so the type carries no size cap; the theorems
require every sampler a reduction outputs to have description length polynomial in its input length
(`PolySizeOut`, `RandPolySizeOut`). -/
abbrev Samp : Type := Σ m : ℕ, MCircuit m

/-- A witness of a learning problem: a single-output circuit `C` (published `KarpLiptonOM.Circuit`)
with `C.1` inputs; its size is the number of gates. -/
abbrev Wit : Type := Σ k : ℕ, Circuit k

/-- The input length `n` of a sampling circuit with `n + 1` outputs. -/
def Samp.len (E : Samp) : ℕ := E.2.outs.length - 1

/-- `E` has at least one output, so it samples pairs `(x, b) ∈ {0,1}ⁿ × {0,1}`. -/
def Samp.WF (E : Samp) : Prop := E.2.outs ≠ []

/-- The sample `(x, b) = E(r)` on coins `r`: the first `n` outputs and the last one. -/
def Samp.sample (E : Samp) (r : List Bool) : List Bool × Bool :=
  ((E.2.eval r).take E.len, (E.2.eval r).getD E.len false)

/-- `(x, b) ∈ supp(E)`. -/
def Samp.IsSample (E : Samp) (x : List Bool) (b : Bool) : Prop :=
  ∃ ρ : Fin E.1 → Bool, E.sample (bits ρ) = (x, b)

/-- `Pr_{(x,b)∼E}[C(x) = b]`, over uniform coins of `E`. -/
noncomputable def Samp.agree (E : Samp) {k : ℕ} (C : Circuit k) : ℝ :=
  coinAvg E.1 (fun ρ => if C.eval (E.sample (bits ρ)).1 = (E.sample (bits ρ)).2 then 1 else 0)

/-- `E` **defines a (partial) boolean function** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 24, p.23 (PDF 25)): no `x`
has both `(x, 0)` and `(x, 1)` in `supp(E)`. -/
def Samp.DefinesFn (E : Samp) : Prop := ∀ x, ¬ (E.IsSample x false ∧ E.IsSample x true)

/-- The first coordinate `X` of `E` has **full support** over `{0,1}ⁿ` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 23,
p.23 (PDF 25)). -/
def Samp.FullSupp (E : Samp) : Prop := ∀ x : List Bool, x.length = E.len → ∃ b, E.IsSample x b

end ProofCryptoSynergy.Supplement


