-- Prove2me | Definitions.Def_ProofCryptoSynergy_Supplement_CGL
-- name    : ProofCryptoSynergy_Supplement_CGL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:46:05.737209+00:00
-- url     : https://prove2.me/theorems/1c9a1742-43c7-4780-912e-413566ba1265
-- title:
--   The learning problems CGL, Total-Learn, Gap-ImpMCSP, Gap-ImpMCSP∗ and Extension-Learn
-- statement:
--   For $s,g,\varepsilon^{-1}:\mathbb N\to\mathbb N$, each problem has as instances at input length $n$ sampling circuits $E$ over $\{0,1\}^n\times\{0,1\}$, restricted as follows, with yes- and no-instances:
--
--   1. **CGL$_{g,\varepsilon}[s]$** (Definition 21): all samplers. Yes: some circuit $C$ of size $\le s(n)$ has $C(x)=b$ for every $(x,b)\in\mathrm{supp}(E)$. No: every circuit $C$ of size $\le g(s(n))$ has $\Pr_{(x,b)\sim E}[C(x)=b]<\tfrac12+\varepsilon(n)$.
--   2. **Total-Learn$_{g,\varepsilon}[s]$** (Definition 23): $X$ has full support. Yes: some $C$ of size $\le s(n)$ has $\Pr[C(x)=b]=1$. No: as for CGL.
--   3. **Gap$_{g,\varepsilon}$-ImpMCSP$[s]$** (Definition 25): $E$ defines a total function $f_E$. Yes: some $C$ of size $\le s(n)$ has $C(x)=f_E(x)$ for all $x$. No: as for CGL.
--   4. **Gap$_{g,\varepsilon}$-ImpMCSP∗$[s]$** (Definition 27): $E$ defines a possibly partial function. Yes: some $C$ of size $\le s(n)$ has $\Pr[C(x)=b]=1$. No: as for CGL.
--   5. **Extension-Learn$_{g,\varepsilon}[s]$** (Definition 73): all samplers. Yes: some $C$ of size $\le s(n)$ has $\Pr[C(x)=b]=1$ and $C(x)=0$ for all $x\notin\mathrm{supp}(X)$. No: every $C$ of size $\le g(n)$ (not $g(s(n))$) has $\Pr[C(x)=b]<\tfrac12+\varepsilon(n)$.
--
--   These promise problems are the targets of the paper's NP-hardness and non-hardness results.
--
--   **Formalization Note** Each is given by witness relations: $R_Y(E,C)$ says $E$ is an instance and $C$ satisfies the yes-condition; $R_N(E,C)$ says $E$ is not an instance, or $C$ has $n$ inputs, the no-size bound and $\Pr\ge\frac12+\varepsilon(n)$. So $N$ is exactly the set of no-instances. The parameter is $\varepsilon^{-1}$, and $\Pr\ge\frac12+\varepsilon(n)$ is written $(\Pr-\frac12)\,\varepsilon^{-1}(n)\ge1$, without division.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definitions 21, 23, 25, 27, pp.22–24 (PDF 24–26); Definition 73, p.53 (PDF 55)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_Supplement_WRel
import Definitions.Def_ProofCryptoSynergy_Supplement_Samp

open KarpLiptonOM LaconicBarrier

namespace ProofCryptoSynergy.Supplement

/-- **CGL** `CGL_{g,ε}[s]` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 21, pp.22–23 (PDF 24–25)). For `s, g, ε⁻¹ : ℕ → ℕ`,
an instance at input length `n` is a sampling circuit `E` over `{0,1}ⁿ × {0,1}`;
* yes: some circuit `C` of size at most `s(n)` has `C(x) = b` for all `(x, b) ∈ supp(E)`;
* no: every circuit `C` of size at most `g(s(n))` has `Pr_{(x,b)∼E}[C(x) = b] < 1/2 + ε(n)`.

**Formalization Note** As witness relations (Definition 3): `R_Y(E, C)` is "`E` is an instance and `C`
satisfies the yes-condition"; `R_N(E, C)` is "`E` is not an instance, or `C` has `n` inputs, size at most
`g(s(n))` and `Pr ≥ 1/2 + ε(n)`", so `N` is exactly the set of no-instances. The parameter is the
function `εinv = ε⁻¹`, and `Pr ≥ 1/2 + ε(n)` is written `1 ≤ (Pr − 1/2) · ε⁻¹(n)`: no division, and
`ε⁻¹(n) = 0` (where `ε(n)` is undefined) puts no circuit in `R_N`. -/
def CGL (s g εinv : ℕ → ℕ) : WRel Samp Wit where
  RY E C := E.WF ∧ C.1 = E.len ∧ C.2.gates.length ≤ s E.len ∧
    ∀ x b, E.IsSample x b → C.2.eval x = b
  RN E C := ¬ E.WF ∨ (C.1 = E.len ∧ C.2.gates.length ≤ g (s E.len) ∧
    1 ≤ (E.agree C.2 - 1 / 2) * (εinv E.len : ℝ))

/-- **Total-Learn** `Total-Learn_{g,ε}[s]` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 23, p.23 (PDF 25)): instances are sampling
circuits whose first coordinate `X` has full support over `{0,1}ⁿ`;
* yes: some circuit `C` of size at most `s(n)` has `Pr_{(x,b)∼E}[C(x) = b] = 1`;
* no: every circuit `C` of size at most `g(s(n))` has `Pr_{(x,b)∼E}[C(x) = b] < 1/2 + ε(n)`.

**Formalization Note** Witness relations and `ε⁻¹` as for `CGL`. -/
def TotalLearn (s g εinv : ℕ → ℕ) : WRel Samp Wit where
  RY E C := (E.WF ∧ E.FullSupp) ∧ C.1 = E.len ∧ C.2.gates.length ≤ s E.len ∧ E.agree C.2 = 1
  RN E C := ¬ (E.WF ∧ E.FullSupp) ∨ (C.1 = E.len ∧ C.2.gates.length ≤ g (s E.len) ∧
    1 ≤ (E.agree C.2 - 1 / 2) * (εinv E.len : ℝ))

/-- **Gap-ImpMCSP** `Gap_{g,ε}-ImpMCSP[s]` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 25, p.24 (PDF 26)): instances are sampling
circuits defining a total boolean function `f_E` (Definition 24);
* yes: some circuit `C` of size at most `s(n)` has `C(x) = f_E(x)` for all `x ∈ {0,1}ⁿ`;
* no: every circuit `C` of size at most `g(s(n))` has `Pr_{(x,b)∼E}[C(x) = b] < 1/2 + ε(n)`.

**Formalization Note** `C(x) = f_E(x)` is written as `C(x) = b` for every `(x, b) ∈ supp(E)`, `x ∈ {0,1}ⁿ`.
Witness relations and `ε⁻¹` as for `CGL`. -/
def GapImpMCSP (s g εinv : ℕ → ℕ) : WRel Samp Wit where
  RY E C := (E.WF ∧ E.DefinesFn ∧ E.FullSupp) ∧ C.1 = E.len ∧ C.2.gates.length ≤ s E.len ∧
    ∀ x : List Bool, x.length = E.len → ∀ b, E.IsSample x b → C.2.eval x = b
  RN E C := ¬ (E.WF ∧ E.DefinesFn ∧ E.FullSupp) ∨ (C.1 = E.len ∧
    C.2.gates.length ≤ g (s E.len) ∧ 1 ≤ (E.agree C.2 - 1 / 2) * (εinv E.len : ℝ))

/-- **Gap-ImpMCSP∗** `Gap_{g,ε}-ImpMCSP∗[s]` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 27, p.24 (PDF 26)): instances are sampling
circuits defining a (possibly partial) boolean function;
* yes: some circuit `C` of size at most `s(n)` has `Pr_{(x,b)∼E}[C(x) = b] = 1`;
* no: every circuit `C` of size at most `g(s(n))` has `Pr_{(x,b)∼E}[C(x) = b] < 1/2 + ε(n)`.

**Formalization Note** Witness relations and `ε⁻¹` as for `CGL`. -/
def GapImpMCSPStar (s g εinv : ℕ → ℕ) : WRel Samp Wit where
  RY E C := (E.WF ∧ E.DefinesFn) ∧ C.1 = E.len ∧ C.2.gates.length ≤ s E.len ∧ E.agree C.2 = 1
  RN E C := ¬ (E.WF ∧ E.DefinesFn) ∨ (C.1 = E.len ∧ C.2.gates.length ≤ g (s E.len) ∧
    1 ≤ (E.agree C.2 - 1 / 2) * (εinv E.len : ℝ))

/-- **Extension-Learn** `Extension-Learn_{g,ε}[s]` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 73, p.53 (PDF 55)): instances are
all sampling circuits over `{0,1}ⁿ × {0,1}`;
* yes: some circuit `C` of size at most `s(n)` has `Pr_{(x,b)∼E}[C(x) = b] = 1` and `C(x) = 0` for every
  `x ∉ supp(X)`;
* no: every circuit `C` of size at most `g(n)` (not `g(s(n))`) has `Pr_{(x,b)∼E}[C(x) = b] < 1/2 + ε(n)`.

**Formalization Note** `x ∉ supp(X)` ranges over `x ∈ {0,1}ⁿ`. Witness relations and `ε⁻¹` as for
`CGL`. -/
def ExtensionLearn (s g εinv : ℕ → ℕ) : WRel Samp Wit where
  RY E C := E.WF ∧ C.1 = E.len ∧ C.2.gates.length ≤ s E.len ∧ E.agree C.2 = 1 ∧
    ∀ x : List Bool, x.length = E.len → (∀ b, ¬ E.IsSample x b) → C.2.eval x = false
  RN E C := ¬ E.WF ∨ (C.1 = E.len ∧ C.2.gates.length ≤ g E.len ∧
    1 ≤ (E.agree C.2 - 1 / 2) * (εinv E.len : ℝ))

end ProofCryptoSynergy.Supplement


