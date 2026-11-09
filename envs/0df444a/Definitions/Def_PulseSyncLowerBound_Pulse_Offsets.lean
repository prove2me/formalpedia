-- Prove2me | Definitions.Def_PulseSyncLowerBound_Pulse_Offsets
-- name    : PulseSyncLowerBound_Pulse_Offsets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:59.081301+00:00
-- url     : https://prove2.me/theorems/a69ac174-d2bf-450f-b21c-3cb03d2f7dd5
-- title:
--   Output paths, signed clock offsets and advancements
-- statement:
--   For $T=\lfloor f/2\rfloor$, define $X=R(T,2)$ and $Y=R(T+1,1)$ from the protocol. A set lies on a $\sigma$-path of $\mathbb Z_q$ when it is contained in $\{c+k\bmod q:0\le k\le\sigma\}$ for some $c$.
--
--   For outputs lying on such a path and $q>2\sigma$, the signed offset $d(a,b)$ is the unique integer in $[-\sigma,\sigma]$ congruent to $b-a$ modulo $q$. Put
--
--   $$D(u,v)=d(\operatorname{out}(u),\operatorname{out}(v)),\qquad
--   \Delta(y)=(\operatorname{out}(Sy)-\operatorname{out}(Py))\bmod q.$$
--
--   Subtraction is performed in the integers before taking a remainder. A compatible output potential satisfies both $\ell(v)-\ell(u)=D(u,v)$ on edges and $\operatorname{out}(u)=\ell(u)\bmod q$ on vertices.
--
--   The signed-offset function is totalized off its source domain by a fixed residue rule. All theorem uses constrain its arguments to actual faces and supply N1, which ensures the source domain. The potential predicate records the requested property; it does not assert existence.
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; §6.1 and §§6.2–6.3, (O1), (O2), equations (6), (8), Lemma 15 clauses; PDF p.20–24 / printed p.18–22; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f.

import Definitions.Def_PulseSyncLowerBound_Pulse_Views
import Definitions.Def_PulseSyncLowerBound_Pulse_Tasks

noncomputable section

namespace PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

variable {n q : ℕ}

/-- Section 6 complexes, computed from the actual protocol, not independent inputs. -/
def X (P : Protocol n (Fin q)) (f : ℕ) := RoundComplex P (f / 2) 2

def Y (P : Protocol n (Fin q)) (f : ℕ) := RoundComplex P (f / 2 + 1) 1

/-- A set of outputs is contained in a σ-path; the path may include unused labels. -/
def OutputsOnPath (σ q : ℕ) (A : Set (Fin q)) : Prop :=
  ∃ c : Fin q, ∀ a ∈ A, ∃ k : ℕ, k ≤ σ ∧
    (a : ℤ) = ((c : ℤ) + (k : ℤ)) % (q : ℤ)

/-- §6.2 (O1)--(O2): the signed offset on a σ-path when q>2σ.
Off this domain this total extension is never used in a conclusion. -/
def signedOffset (σ q : ℕ) (a b : Fin q) : ℤ :=
  let r := ((b : ℤ) - (a : ℤ)) % (q : ℤ)
  if r ≤ (σ : ℤ) then r else r - (q : ℤ)

/-- Equation (6). -/
def D (P : Protocol n (Fin q)) (f σ : ℕ)
    (u v : TaggedView P (f / 2)) : ℤ :=
  signedOffset σ q (viewOutput P (f / 2) u) (viewOutput P (f / 2) v)

/-- Equation (8), signed subtraction before taking the nonnegative remainder. -/
def advancement (P : Protocol n (Fin q)) (f : ℕ)
    (y : TaggedView P (f / 2 + 1)) : ℤ :=
  (((viewOutput P (f / 2) (viewSuffix P (f / 2) y)).val : ℤ) -
    ((viewOutput P (f / 2) (viewPrefix P (f / 2) y)).val : ℤ)) % (q : ℤ)

/-- Both clauses of Lemma 15, with constraints only on actual vertices/edges. -/
def OutputPotential (P : Protocol n (Fin q)) (f σ : ℕ)
    (ℓ : TaggedView P (f / 2) → ℤ) : Prop :=
  (∀ u v, IsEdge (X P f) u v → ℓ v - ℓ u = D P f σ u v) ∧
    ∀ u, {u} ∈ X P f → ((viewOutput P (f / 2) u).val : ℤ) = ℓ u % (q : ℤ)

end PulseSyncLowerBound.Pulse


