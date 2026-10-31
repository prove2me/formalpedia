-- Prove2me | Definitions.Def_MinimalAccess_Mechanism
-- name    : MinimalAccess_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:42:06.352272+00:00
-- url     : https://prove2.me/theorems/cb40e732-c06d-4340-86b1-f7907744895b
-- title:
--   Mechanisms: (minimal-access) stability, strategy-proofness, minimal-access monotonicity
-- statement:
--   With students, schools and capacities fixed, a **mechanism** $\varphi$ selects for each problem $(P,\succ,r)$ a matching $\varphi(P,\succ,r)$; $\varphi_i(P,\succ,r)$ is student $i$'s assignment. The mechanism is **stable** / **minimal-access stable** if $\varphi(P,\succ,r)$ is stable / minimal-access stable for every problem. It is
--
--   1. **strategy-proof** if for every problem, every student $i$ and every preference $P'_i$: $\varphi_i(P,\succ,r)\;R_i\;\varphi_i(P'_i,P_{-i},\succ,r)$;
--   2. **minimal-access monotonic** if for every student $i$ and all problems $(P,\succ,r)$, $(P,\succ,r')$ with $r'(i)\subseteq r(i)$ and $r'(j)=r(j)$ for all $j\neq i$: $\varphi_i(P,\succ,r)\;R_i\;\varphi_i(P,\succ,r')$.
--
--   Minimal-access monotonicity says that hiding or renouncing minimal-access rights never helps a student. These are the three axioms of Theorem 1.
--
--   **Formalization Note** `Mechanism n m` is the type of functions of `(P, pri, r)` to assignments; `IsMechanism q φ` says every output respects the capacities. $R_i$ is `≤` on the ranks of the true preference `P i`, and $(P'_i,P_{-i})$ is `Function.update P i P'`.
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), p.11 (mechanism, (minimal-access) stable mechanism, minimal-access monotonicity, strategy-proofness)

import Mathlib
import Definitions.Def_MinimalAccess_Model

namespace MinimalAccess

/-!
Klaus–Klijn, *Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism*,
BSE Working Paper 1264 (rev. July 2023), p.11: mechanisms and their properties. "A mechanism φ
is a function that selects for each problem (P, ≻, r) a matching φ(P, ≻, r). … Mechanism φ is
individually rational / non-wasteful / (minimal-access) stable if for each problem (P, ≻, r),
φ(P, ≻, r) is individually rational / non-wasteful / (minimal-access) stable." "Formally,
mechanism φ is minimal-access monotonic if for each student i and for each pair of problems
(P, ≻, r) and (P, ≻, r′) with r′(i) ⊆ r(i) and for each student j ≠ i, r′(j) = r(j), we have
φ_i(P, ≻, r) R_i φ_i(P, ≻, r′)." "Formally, mechanism φ is strategy-proof if for each problem
(P, ≻, r), for each student i, and for all preferences P′_i ∈ 𝒫_i, φ_i(P, ≻, r) R_i
φ_i(P′_i, P_{-i}, ≻, r) where P_{-i} ≡ (P_j)_{j≠i}."

**Formalization Note.** The students `Fin n`, schools `Fin m` and capacities `q` are fixed
(p.5), so a mechanism is a function of `(P, ≻, r)`. Its value is an assignment; that it is a
matching (capacities respected) is the predicate `IsMechanism q φ`, assumed wherever the paper
speaks of a mechanism. `R_i` is `≤` on the ranks of the **true** preference `P i`.
-/

open GaleShapley1962.Admissions

/-- A mechanism for fixed `I = Fin n`, `S = Fin m`: a function of the problem `(P, ≻, r)`. -/
abbrev Mechanism (n m : ℕ) :=
  (Fin n → Pref m) → (Fin m → Prio n) → (Fin n → Finset (Fin m)) → Assignment n m

/-- `φ` selects a matching for each problem (p.11): `|φ(P, ≻, r)(s)| ≤ q_s` everywhere. -/
def IsMechanism {n m : ℕ} (q : Fin m → ℕ) (φ : Mechanism n m) : Prop :=
  ∀ P pri r, IsMatching q (φ P pri r)

/-- `φ` is stable (p.11): `φ(P, ≻, r)` is stable for every problem. -/
def IsStableMech {n m : ℕ} (q : Fin m → ℕ) (φ : Mechanism n m) : Prop :=
  ∀ P pri r, IsStable q P pri r (φ P pri r)

/-- `φ` is minimal-access stable (p.11): `φ(P, ≻, r)` is minimal-access stable for every
problem. -/
def IsMinimalAccessStableMech {n m : ℕ} (q : Fin m → ℕ) (φ : Mechanism n m) : Prop :=
  ∀ P pri r, IsMinimalAccessStable q P pri r (φ P pri r)

/-- Strategy-proofness (p.11): `φ_i(P, ≻, r) R_i φ_i(P′_i, P_{-i}, ≻, r)` for every problem,
student `i` and preference `P′_i`. -/
def IsStrategyProof {n m : ℕ} (φ : Mechanism n m) : Prop :=
  ∀ (P : Fin n → Pref m) pri r (i : Fin n) (P' : Pref m),
    P i (φ P pri r i) ≤ P i (φ (Function.update P i P') pri r i)

/-- Minimal-access monotonicity (p.11): if `r′(i) ⊆ r(i)` and `r′(j) = r(j)` for every `j ≠ i`,
then `φ_i(P, ≻, r) R_i φ_i(P, ≻, r′)`. -/
def IsMinimalAccessMonotonic {n m : ℕ} (φ : Mechanism n m) : Prop :=
  ∀ (P : Fin n → Pref m) pri (r r' : Fin n → Finset (Fin m)) (i : Fin n),
    r' i ⊆ r i → (∀ j, j ≠ i → r' j = r j) → P i (φ P pri r i) ≤ P i (φ P pri r' i)

end MinimalAccess


