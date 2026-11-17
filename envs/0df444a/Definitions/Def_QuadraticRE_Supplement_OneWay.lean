-- Prove2me | Definitions.Def_QuadraticRE_Supplement_OneWay
-- name    : QuadraticRE_Supplement_OneWay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:53:29.563406+00:00
-- url     : https://prove2.me/theorems/2d7765fc-d6c6-4442-a061-6889da4d0953
-- title:
--   One-way function families and one-way functions in polynomial-time uniform $\mathrm{NC}^1$
-- statement:
--   A family $f_\kappa:\{0,1\}^{n(\kappa)}\to\{0,1\}^{m(\kappa)}$ is **one-way** if for every nonuniform probabilistic polynomial-time inverter $A$,
--   $$\Pr_{x\leftarrow\{0,1\}^{n(\kappa)}}\Big[f_\kappa\big(A(1^\kappa,f_\kappa(x))\big)=f_\kappa(x)\Big]$$
--   is negligible in $\kappa$; the inverter succeeds when it finds any preimage, not necessarily $x$.
--
--   **One-way functions exist in polynomial-time uniform $\mathrm{NC}^1$** if there are Boolean circuits $C_\kappa$ of fan-in at most two, produced from $1^\kappa$ by one polynomial-time machine, of depth at most $c\,(1+\log_2\kappa)$ for a constant $c$, that compute a one-way family.
--
--   These are the hypothesis and the security notion of Theorem 5.5.
--
--   **Formalization Note** An inverter is the published `QuadraticRE.Distinguisher` (a fixed polynomial-time machine with polynomial advice and coins) whose output string, truncated or padded with zeros, is the candidate preimage. The depth is bounded in the security parameter; since $C_\kappa$ is produced in polynomial time its input length is polynomial in $\kappa$, so the usual bound $O(\log n(\kappa))$ implies this one.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), §3.1, p.13; §5.2, Theorem 5.5, p.33

import Mathlib
import Definitions.Def_QuadraticRE_CompPrivate
import Definitions.Def_QuadraticRE_Supplement_Circuit

namespace QuadraticRE.Supplement

open QuadraticRE

/-- The output string of a nonuniform probabilistic polynomial-time algorithm `A` on `z` with coins
`ω`, with the same input layout `(1^κ, a_κ, z, ω)` as the base mission's `Distinguisher.Accepts`. -/
def runAdv (A : Distinguisher) (κ : ℕ) (z : List Bool) (ω : Fin (A.coins κ) → F2) : List Bool :=
  A.D (encNat κ ++ encNat (A.advice κ).length ++ A.advice κ ++ encNat z.length ++ z ++ bits ω)

/-- A bit string read as a vector of length `n`: truncated, or padded with zeros. -/
def ofBits (n : ℕ) (l : List Bool) : Fin n → F2 := fun i => if l.getD i.val false then 1 else 0

/-- One-wayness of a family `f_κ : F₂^{n κ} → F₂^{m κ}` (Orsini, Patra, *From Degree Three to Degree
Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §3.1, p.13 conventions, used in §5.2, p.33):
for every nonuniform probabilistic polynomial-time inverter `A`, the probability over a uniform
`x ∈ F₂^{n κ}` and `A`'s coins that `A(1^κ, f_κ(x))` outputs **some** preimage of `f_κ(x)` is
negligible in `κ`.

**Formalization Note.** An inverter is the base mission's `Distinguisher` (one polynomial-time
machine, polynomial advice and coins), whose output string is read as a candidate preimage by
`ofBits`. Inversion succeeds on any preimage, not only on `x`. -/
def IsOneWay (n m : ℕ → ℕ) (f : ∀ κ, (Fin (n κ) → F2) → Fin (m κ) → F2) : Prop :=
  ∀ A : Distinguisher,
    Negligible fun κ =>
      prob (fun ω : (Fin (n κ) → F2) × (Fin (A.coins κ) → F2) =>
        f κ (ofBits (n κ) (runAdv A κ (bits (f κ ω.1)) ω.2)) = f κ ω.1)

/-- "One-way functions exist in polynomial-time uniform `NC¹`" (§5.2, Theorem 5.5, p.33): there are a
sequence of Boolean circuits `C_κ` of fan-in at most two, one polynomial-time machine mapping `1^κ` to
the encoding of `C_κ`, and a constant `c` with `depth C_κ ≤ c · (1 + log₂ κ)`, such that the functions
the circuits compute form a one-way family.

**Formalization Note.** Depth is bounded by `O(log κ)` in the security parameter. Because `C_κ` is
produced in polynomial time, its input length is at most polynomial in `κ`, so the usual bound
`O(log n(κ))` implies this one: this hypothesis is the more permissive one. -/
def OWFInUniformNC1 : Prop :=
  ∃ (Cs : ℕ → Circuit) (c : ℕ),
    PolyTimeFn encNat (fun κ => encCircuit (Cs κ)) ∧
    (∀ κ, (Cs κ).depth ≤ c * (1 + Nat.log 2 κ)) ∧
    IsOneWay (fun κ => (Cs κ).N) (fun κ => (Cs κ).b) (fun κ => (Cs κ).eval)

end QuadraticRE.Supplement


