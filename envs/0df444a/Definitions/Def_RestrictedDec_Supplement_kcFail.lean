-- Prove2me | Definitions.Def_RestrictedDec_Supplement_kcFail
-- name    : RestrictedDec_Supplement_kcFail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:29:18.993255+00:00
-- url     : https://prove2.me/theorems/2f4c2c3d-587e-4562-b97c-a46fd215f12c
-- title:
--   Keywise correctness (KC) of the label scheme and its failure probability $\delta_L$
-- statement:
--   For a label scheme $L$ with label space $\{0,1\}^{\ell(\lambda)}$, the **keywise-correctness failure probability** is
--   $$\delta_L(\lambda)=\Pr_{(pk,sk)\leftarrow\mathrm{KeyGen}_L(1^\lambda)}\Big[\neg\ \forall y\in\{0,1\}^{\ell(\lambda)}\ \forall r\in\mathrm{Coins}_L:\ \mathrm{Dec}_{sk}(\mathrm{Enc}_{pk}(y;r))=y\Big],$$
--   and $L$ is **keywise correct** (KC) if $\delta_L$ is negligible (Definition 4). The bound covers every label and every allowed randomness, including encryption coins chosen by the adversary; $\delta_L$ is the term $12\delta_L$ of (B.5) and $2\delta_L$ of Theorem 11.
--
--   **Formalization Note** $\mathrm{Coins}_L$ is the set of all encryption coin vectors of $L$: honest label encryption draws uniformly from all of them.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 4, p.29; (KC), p.35

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_PKE
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

open Classical in
/-- The **keywise-correctness failure probability** `δ_L(λ)` of a label scheme `L` with label
space `{0,1}^{ℓ(λ)}`: the probability over `(pk, sk) ← KeyGen_L(1^λ)` that some label
`y ∈ {0,1}^{ℓ(λ)}` and some allowed coins `r ∈ Coins_L` give `Dec_sk(Enc_pk(y; r)) ≠ y`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 4, p.29; (KC), p.35
("except with negligible probability δL(λ) over the label key pair, ∀y ∈ {0, 1}ℓ(λ) ∀r ∈ CoinsL :
Decsk(Encpk(y; r)) = y").

**Formalization Note.** `Coins_L` is the set of all encryption coin vectors of `L`
(`Fin (encCoins λ) → Bool`): honest label encryption draws uniformly from all of them, and the
relations (B.1), (B.4) check that a claimed coin string has exactly this length. -/
noncomputable def kcFail (L : PKE) (ℓ : ℕ → ℕ) (lam : ℕ) : ℝ :=
  (((L.keyLaw lam).map fun k => decide (¬ ∀ y : Str, y.length = ℓ lam →
    ∀ ρ : Fin (L.encCoins lam) → Bool, L.dec lam k.2 (L.enc lam k.1 y ρ) = some y)) true).toReal

/-- **Keywise correctness** (KC) of the label scheme `L` (Definition 4): `δ_L` is negligible. -/
def KeywiseCorrect (L : PKE) (ℓ : ℕ → ℕ) : Prop := NoisyOWMPC.Negligible (kcFail L ℓ)

end Supplement

end RestrictedDec


