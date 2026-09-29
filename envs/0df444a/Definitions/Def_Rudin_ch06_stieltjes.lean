-- Prove2me | Definitions.Def_Rudin_ch06_stieltjes
-- name    : Rudin_ch06_stieltjes
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T20:04:20.562817+00:00
-- url     : https://prove2.me/theorems/919be3fb-1469-4695-a98d-81c3c1f67aff
-- title:
--   The Riemann–Stieltjes integral $\int_a^b f\,d\alpha$
-- statement:
--   Rudin's Definitions 6.1–6.3, formalized. A **partition** of $[a,b]$ is a finite increasing list $a = x_0 \le x_1 \le \dots \le x_n = b$; for a bounded $f$ and a monotonically increasing integrator $\alpha$ the **upper** and **lower sums** are $U(P,f,\alpha) = \sum_i M_i \Delta\alpha_i$ and $L(P,f,\alpha) = \sum_i m_i \Delta\alpha_i$, with $M_i$ and $m_i$ the supremum and infimum of $f$ on the $i$-th subinterval and $\Delta\alpha_i = \alpha(x_i) - \alpha(x_{i-1})$. The **upper** and **lower integrals** are the infimum of $U$ and the supremum of $L$ over all partitions; $f$ is **integrable with respect to $\alpha$** when they coincide, and $\int_a^b f\,d\alpha$ is the common value. The case $\alpha(x) = x$ is the Riemann integral. Mathlib has no Riemann–Stieltjes integral, so this construction is new; the suprema and infima are the usual real ones, which return $0$ on unbounded sets, so the theorems below state Rudin's boundedness hypotheses explicitly.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, pp. 120-122, Definitions 6.1, 6.2, 6.3

import Mathlib

/-!
# Rudin, Chapter 6 — the Riemann–Stieltjes integral

Definitions transcribed from Walter Rudin, *Principles of Mathematical Analysis*, 3rd edition,
Chapter 6 (Definitions 6.1, 6.2, 6.3).

Mathlib has the Bochner and interval integrals, but no Riemann–Stieltjes integral
`∫ f dα` for a monotonically increasing integrator `α`, which is the object Chapter 6 is about;
it is therefore built here from Rudin's definitions: partitions, upper and lower sums, upper and
lower integrals, and integrability as their equality.  Taking `α x = x` recovers the Riemann
integral, as Rudin notes, and `Rudin.RiemannIntegrable` is that special case.

All suprema and infima are Mathlib's `sSup`/`sInf` on `ℝ`, which return `0` for sets that are
empty or unbounded; every statement about these notions therefore carries the boundedness
hypotheses Rudin states.
-/

namespace Rudin

/-- Rudin, Definition 6.1: a **partition** of `[a, b]` is a finite set of points
`a = x₀ ≤ x₁ ≤ ⋯ ≤ xₙ = b`, recorded here as the number `n` of subintervals together with the
(monotone) placement function `x`. -/
structure Partition (a b : ℝ) where
  /-- The number of subintervals of the partition. -/
  n : ℕ
  /-- The division points; only the values at `0, 1, …, n` matter. -/
  x : ℕ → ℝ
  /-- The partition starts at `a`. -/
  first : x 0 = a
  /-- The partition ends at `b`. -/
  last : x n = b
  /-- The division points increase. -/
  mono : ∀ i < n, x i ≤ x (i + 1)

/-- Rudin, Definition 6.3: `P'` is a **refinement** of `P` if every division point of `P` is
also a division point of `P'`. -/
def Refines {a b : ℝ} (P' P : Partition a b) : Prop :=
  ∀ i ≤ P.n, ∃ j ≤ P'.n, P'.x j = P.x i

/-- Rudin, Definition 6.2: the upper sum `U(P, f, α) = ∑ Mᵢ Δαᵢ`, where `Mᵢ` is the supremum of
`f` on the `i`-th subinterval. -/
noncomputable def upperSum {a b : ℝ} (f α : ℝ → ℝ) (P : Partition a b) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) * (α (P.x (i + 1)) - α (P.x i))

/-- Rudin, Definition 6.2: the lower sum `L(P, f, α) = ∑ mᵢ Δαᵢ`, where `mᵢ` is the infimum of
`f` on the `i`-th subinterval. -/
noncomputable def lowerSum {a b : ℝ} (f α : ℝ → ℝ) (P : Partition a b) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) * (α (P.x (i + 1)) - α (P.x i))

/-- Rudin, Definition 6.2, equation (5): the **upper integral** `inf_P U(P, f, α)`. -/
noncomputable def upperIntegral (a b : ℝ) (f α : ℝ → ℝ) : ℝ :=
  sInf {y : ℝ | ∃ P : Partition a b, y = upperSum f α P}

/-- Rudin, Definition 6.2, equation (6): the **lower integral** `sup_P L(P, f, α)`. -/
noncomputable def lowerIntegral (a b : ℝ) (f α : ℝ → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ P : Partition a b, y = lowerSum f α P}

/-- Rudin, Definition 6.2: `f ∈ ℛ(α)` on `[a, b]`, i.e. the upper and lower integrals agree. -/
def RSIntegrable (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  upperIntegral a b f α = lowerIntegral a b f α

/-- Rudin, Definition 6.2, equation (7): the Riemann–Stieltjes integral `∫ₐᵇ f dα`, defined as
the common value of the upper and lower integrals when `f ∈ ℛ(α)` (and as the upper integral
otherwise). -/
noncomputable def RSIntegral (a b : ℝ) (f α : ℝ → ℝ) : ℝ :=
  upperIntegral a b f α

/-- Rudin, Definition 6.1: `f ∈ ℛ` on `[a, b]`, the Riemann-integrable case `α x = x`. -/
def RiemannIntegrable (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  RSIntegrable a b f id

/-- The Riemann integral `∫ₐᵇ f dx`, the case `α x = x` of `Rudin.RSIntegral`. -/
noncomputable def RiemannIntegral (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  RSIntegral a b f id

end Rudin


