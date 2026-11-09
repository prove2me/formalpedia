-- Prove2me | Definitions.Def_QMAvsQCIP_BBProver
-- name    : QMAvsQCIP_BBProver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:22.918529+00:00
-- url     : https://prove2.me/theorems/a21a3e8a-daeb-4ca7-ad76-8418bad5d50d
-- title:
--   Deterministic prover in the query model
-- statement:
--   A **deterministic prover** with $\ell$-bit messages in the query complexity model maps the list $[a_0,\dots,a_j]$ of verifier messages received so far to its reply $b_j\in\{0,1\}^\ell$.
--
--   By Lemma 1(3), such strategies attain the maximum acceptance over all provers. Provers are quantified after the oracle (or are given as functions of it), so they may depend on every value of $O$.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 5, p.17; Lemma 1(3), p.16

import Mathlib

set_option autoImplicit false

namespace QMAvsQCIP

/-- A **deterministic prover in the query complexity model** with `ℓ`-bit messages: it maps the
list `[a₀, …, a_j]` of verifier messages received so far to its reply `b_j ∈ {0,1}^ℓ`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 5, p.17 (PDF p.20): "As in the computational model, classical
transcript-dependent provers suffice by the lemma on classical prover strategies (Lemma 1)";
Lemma 1(3), p.16 (PDF p.19): "a deterministic strategy specifying one reply for each transcript
attains the maximum acceptance probability over all provers"; Definition 3, p.16: "Witnesses and
prover strategies may depend on every value of O".

**Formalization Note.** Provers are quantified after the oracle (or are functions of it), so
they may depend on all of `O`. -/
abbrev BBProver (ℓ : ℕ) : Type := List (Fin ℓ → Bool) → (Fin ℓ → Bool)

end QMAvsQCIP


