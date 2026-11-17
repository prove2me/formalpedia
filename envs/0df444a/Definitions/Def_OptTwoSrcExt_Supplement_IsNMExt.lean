-- Prove2me | Definitions.Def_OptTwoSrcExt_Supplement_IsNMExt
-- name    : OptTwoSrcExt_Supplement_IsNMExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:36:13.325792+00:00
-- url     : https://prove2.me/theorems/dae9ec69-36fd-4deb-b35f-aa96aeae4759
-- title:
--   Admissible tamperings, $t$-non-malleable and separately source-strong two-source extraction
-- statement:
--   Let $X,Y$ be independent sources (arbitrary probability distributions on finite sets) and let $E(x,y)$ take values in a finite output set $\{0,1\}^m$.
--
--   1. A pair of separate maps $(f,g)$ is **admissible** for $(X,Y)$ if $\Pr[(f(X),g(Y))=(X,Y)]=0$. The maps are otherwise arbitrary; nothing is assumed about the entropy of $f(X)$, $g(Y)$.
--   2. For admissible pairs $(f_j,g_j)_{j=1}^t$ write $T=(E(f_j(X),g_j(Y)))_{j=1}^t$ for the actual tampered outputs. $E$ is a **$t$-non-malleable two-source extractor at entropy $k$ with error $\varepsilon$** if for all independent $X,Y$ with $H_\infty(X),H_\infty(Y)\ge k$ and all admissible $t$-tuples
--   $$\Delta\big((E(X,Y),T),\,(U_m,T)\big)\le\varepsilon,$$
--   where $U_m$ is uniform and independent of $T$ (Definition 2.2).
--   3. $E$ is **separately source strong with error $\xi$ at entropy $k$** if for all such sources and tamperings, with $Z=E(X,Y)$,
--   $$\Delta\big((Z,T,X),(U_m,T,X)\big)\le\xi,\qquad \Delta\big((Z,T,Y),(U_m,T,Y)\big)\le\xi,$$
--   with $U_m$ independent of the displayed $(T,X)$, respectively $(T,Y)$ (Definition 2.3).
--
--   For $t=0$ the tuple $T$ is empty and these are ordinary extraction and ordinary extraction strong in either source. These notions state the non-malleable endpoints of the paper (Theorems 3.64, 4.8, 5.18) and the advice bound of Theorem 5.10.
--
--   **Formalization Note** Min-entropy, statistical distance and the law of an independent pair are the published `FuzzyExtractors.Hamming.minEntropy`, `statDist` and `LowErrExt.indepPair`. The tamperings may repeat.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Definitions 2.2 and 2.3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair

open FuzzyExtractors.Hamming LowErrExt

namespace OptTwoSrcExt.Supplement

/-- **Admissible separate tampering `(f, g)` for the sources `(X, Y)`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Definition 2.2, printed p.14 (PDF p.16): "arbitrary
separate maps fj, gj satisfying Pr[(fj(X), gj(Y)) = (X, Y)] = 0".

`IsAdmissible X Y f g`: for independent `X, Y`, the event `(f(X), g(Y)) = (X, Y)` has probability
zero. The maps are otherwise arbitrary (no entropy assumption on `f(X)`, `g(Y)`). -/
def IsAdmissible {A B : Type*} (X : PMF A) (Y : PMF B) (f : A → A) (g : B → B) : Prop :=
  (indepPair X Y).toOuterMeasure {p | f p.1 = p.1 ∧ g p.2 = p.2} = 0

/-- **The actual tampered-output tuple** `(E(f_j(x), g_j(y)))_{j=1}^t`. -/
def tamperTuple {A B O : Type*} {t : ℕ} (E : A → B → O) (f : Fin t → A → A) (g : Fin t → B → B)
    (x : A) (y : B) : Fin t → O :=
  fun j => E (f j x) (g j y)

/-- **`t`-non-malleable two-source extractor at entropy `k` and error `ε`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Definition 2.2, printed p.14 (PDF p.16): "A map
E : {0, 1}^n × {0, 1}^n → {0, 1}^m is a t-non-malleable two-source extractor at entropy k and error
ε if, for independent sources X, Y of entropy at least k and arbitrary separate maps fj, gj
satisfying Pr[(fj(X), gj(Y)) = (X, Y)] = 0, one has
∆((E(X, Y), (E(fj(X), gj(Y)))_{j=1}^t), (Um, (E(fj(X), gj(Y)))_{j=1}^t)) ⩽ ε. The fresh uniform
variable is independent of the actual joint tampered-output law. No entropy assumption is made on
tampered inputs. For t = 0 the comparison tuple is empty and the definition is ordinary two-source
extraction."

`IsNMExt t k ε E`: for all sources `X, Y` with `H∞ ≥ k` and all `t`-tuples of admissible separate
tamperings, the joint law of `(E(X, Y), T)`, `T` the actual tampered-output tuple, is within `ε` of
`U ⊗ law(T)`, `U` uniform on the output type and independent of `T`.

**Formalization Note.** Min-entropy and statistical distance are the published
`FuzzyExtractors.Hamming.minEntropy` and `statDist`; sources are arbitrary probability mass functions.
The tamperings may repeat. At `t = 0` the tuple type `Fin 0 → O` has one point, and the condition is
ordinary extraction. -/
def IsNMExt {A B O : Type*} [Fintype O] [Nonempty O] (t : ℕ) (k ε : ℝ) (E : A → B → O) : Prop :=
  ∀ (X : PMF A) (Y : PMF B), k ≤ minEntropy X → k ≤ minEntropy Y →
    ∀ (f : Fin t → A → A) (g : Fin t → B → B), (∀ j, IsAdmissible X Y (f j) (g j)) →
      statDist ((indepPair X Y).map fun p => (E p.1 p.2, tamperTuple E f g p.1 p.2))
        (indepPair (PMF.uniformOfFintype O)
          ((indepPair X Y).map fun p => tamperTuple E f g p.1 p.2)) ≤ ε

/-- **Separately source-strong `t`-non-malleable extraction with error `ξ` at entropy `k`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Definition 2.3, printed p.14 (PDF p.16): "Let Z = F(X, Y),
and, for an admissible tuple of t separate tamperings, put Tj = F(fj(X), gj(Y)) and
T = (T1, . . . , Tt). A t-non-malleable function F is source strong with error ξ at component entropy
k if, for all independent k-sources and all such tamperings, ∆((Z, T, X), (Um, T, X)) ⩽ ξ,
∆((Z, T, Y), (Um, T, Y)) ⩽ ξ. The two guarantees are separate; neither discloses (X, Y) jointly."

`IsSourceStrongNM t k ξ E`: for all sources with `H∞ ≥ k` and all admissible `t`-tuples, both
`Δ((Z, T, X), (U, T, X)) ≤ ξ` and `Δ((Z, T, Y), (U, T, Y)) ≤ ξ`, with `U` uniform on the output type
and independent of the displayed `(T, X)` resp. `(T, Y)`.

**Formalization Note.** As in `IsNMExt`; `t = 0` is ordinary extraction strong in either source. -/
def IsSourceStrongNM {A B O : Type*} [Fintype O] [Nonempty O] (t : ℕ) (k ξ : ℝ) (E : A → B → O) :
    Prop :=
  ∀ (X : PMF A) (Y : PMF B), k ≤ minEntropy X → k ≤ minEntropy Y →
    ∀ (f : Fin t → A → A) (g : Fin t → B → B), (∀ j, IsAdmissible X Y (f j) (g j)) →
      statDist ((indepPair X Y).map fun p => (E p.1 p.2, tamperTuple E f g p.1 p.2, p.1))
          (indepPair (PMF.uniformOfFintype O)
            ((indepPair X Y).map fun p => (tamperTuple E f g p.1 p.2, p.1))) ≤ ξ ∧
        statDist ((indepPair X Y).map fun p => (E p.1 p.2, tamperTuple E f g p.1 p.2, p.2))
          (indepPair (PMF.uniformOfFintype O)
            ((indepPair X Y).map fun p => (tamperTuple E f g p.1 p.2, p.2))) ≤ ξ

end OptTwoSrcExt.Supplement


