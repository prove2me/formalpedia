-- Prove2me | Definitions.Def_MinimalAccess_StudentTypes
-- name    : MinimalAccess_StudentTypes
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:42:01.388015+00:00
-- url     : https://prove2.me/theorems/6491e5d4-860f-4e53-aabe-f8170da2649f
-- title:
--   Condition (t.b) and the student types of the Type Claim
-- statement:
--   Let $\mu$ and $\mu^*$ be two matchings (in the paper $\mu=\varphi(P,\succ,r)$ and $\mu^*=\gamma(P,\succ,r)$). Condition **(t.b)** says that every student $\ell$ with $\mu(\ell)\neq\mu^*(\ell)$ finds exactly one school acceptable under $P_\ell$. A student $\ell$ is of
--
--   - **Type 1** if $\mu^*(\ell)\in S$ is the only acceptable school under $P_\ell$ and $\mu(\ell)=\emptyset$;
--   - **Type 2** if $\mu(\ell)\in S$ is the only acceptable school under $P_\ell$ and $\mu^*(\ell)=\emptyset$;
--   - **Type 3** if $\mu(\ell)=\mu^*(\ell)\,R_\ell\,\emptyset$.
--
--   These notions organize the uniqueness proof of Theorem 1 in Appendix A.
--
--   **Formalization Note** "$s$ is the only acceptable school" is `∀ t, Acceptable P ℓ t ↔ t = s`; (t.b) uses `∃! s, Acceptable P ℓ s`. The predicates take the two assignments as arguments.
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Appendix A, Claim 1 (t.b.), p.22, and Claim 2 (Type Claim), p.23

import Mathlib
import Definitions.Def_MinimalAccess_Model

namespace MinimalAccess

/-!
Klaus–Klijn, *Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism*,
BSE Working Paper 1264 (rev. July 2023), Appendix A, Claim 1 (t.b) p.22 and Claim 2 p.23: the
condition that every student with different matches finds only one school acceptable, and the
three student types. With `μ = φ(P, ≻, r)` and `μ* = γ(P, ≻, r)`: "Type 1: γ_ℓ(P, ≻, r) ∈ S is
the only acceptable school under P_ℓ and φ_ℓ(P, ≻, r) = ∅. Type 2: φ_ℓ(P, ≻, r) ∈ S is the only
acceptable school under P_ℓ and γ_ℓ(P, ≻, r) = ∅. Type 3: φ_ℓ(P, ≻, r) = γ_ℓ(P, ≻, r) R_ℓ ∅."

**Formalization Note.** The predicates take the two matchings `μ` (the role of `φ(P, ≻, r)`)
and `μstar` (the role of `γ(P, ≻, r)`) as arguments. "Only one school is acceptable" is
`∃! s, Acceptable P ℓ s`; "`x ∈ S` is the only acceptable school" is `x = some s` with
`∀ t, Acceptable P ℓ t ↔ t = s`.
-/

open GaleShapley1962.Admissions

/-- `s` is the only acceptable school for student `ℓ` under `P_ℓ`. -/
def OnlyAcceptable {n m : ℕ} (P : Fin n → Pref m) (ℓ : Fin n) (s : Fin m) : Prop :=
  ∀ t, Acceptable P ℓ t ↔ t = s

/-- Condition (t.b) (p.22): every student `ℓ` with `μ(ℓ) ≠ μ*(ℓ)` finds exactly one school
acceptable under `P_ℓ`. -/
def OneAcceptableWhereDiffer {n m : ℕ} (P : Fin n → Pref m) (μ μstar : Assignment n m) : Prop :=
  ∀ ℓ, μ ℓ ≠ μstar ℓ → ∃! s, Acceptable P ℓ s

/-- Type 1 (p.23): `μ*(ℓ) ∈ S` is the only acceptable school under `P_ℓ` and `μ(ℓ) = ∅`. -/
def IsType1 {n m : ℕ} (P : Fin n → Pref m) (μ μstar : Assignment n m) (ℓ : Fin n) : Prop :=
  (∃ s, μstar ℓ = some s ∧ OnlyAcceptable P ℓ s) ∧ μ ℓ = none

/-- Type 2 (p.23): `μ(ℓ) ∈ S` is the only acceptable school under `P_ℓ` and `μ*(ℓ) = ∅`. -/
def IsType2 {n m : ℕ} (P : Fin n → Pref m) (μ μstar : Assignment n m) (ℓ : Fin n) : Prop :=
  (∃ s, μ ℓ = some s ∧ OnlyAcceptable P ℓ s) ∧ μstar ℓ = none

/-- Type 3 (p.23): `μ(ℓ) = μ*(ℓ) R_ℓ ∅`. -/
def IsType3 {n m : ℕ} (P : Fin n → Pref m) (μ μstar : Assignment n m) (ℓ : Fin n) : Prop :=
  μ ℓ = μstar ℓ ∧ P ℓ (μ ℓ) ≤ P ℓ none

end MinimalAccess


