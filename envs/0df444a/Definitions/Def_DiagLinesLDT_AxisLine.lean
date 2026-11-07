-- Prove2me | Definitions.Def_DiagLinesLDT_AxisLine
-- name    : DiagLinesLDT_AxisLine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:00.120668+00:00
-- url     : https://prove2.me/theorems/292d6344-789e-4d80-81bc-c053eaf9fbf9
-- title:
--   Axis-parallel lines of $\mathbb F_q^m$ as point sets, and legal answers of degree at most $d$
-- statement:
--   For $u\in\mathbb F_q^m$ and a coordinate $i$, the **axis-parallel line** through $u$ in direction $e_i$ is the set of points
--
--   $$\ell=\{u+te_i : t\in\mathbb F_q\}.$$
--
--   A function $f:\ell\to\mathbb F_q$ is a **legal answer of degree at most $d$** when there is a univariate polynomial $p$ of degree at most $d$ with $f(u+te_i)=p(t)$ for all $t$, for some parametrization $t\mapsto u+te_i$ of $\ell$.
--
--   These are the questions and the answers of the line player in the axis-parallel lines test. The question is the set $\ell$ and carries no distinguished point of it, which is what makes the test a real constraint on that player.
--
--   **Formalization Note** A line is a subtype of sets of points, never a pair $(u,i)$. Legal answers are functions on $\ell$, as the source writes them, so over $\mathbb F_2$ a line has 4 legal answers, and for $d\ge q-1$ every function is legal. Legality does not depend on the parametrization, because changing the base point translates $t$.
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Definitions 2.1 and 2.4, pp.4–5

import Mathlib

open Polynomial

namespace DiagLinesLDT

variable {F : Type*} [Field F] {m : ℕ}

/-- The set `{u + t e_i : t ∈ 𝔽_q}`, the axis-parallel line through `u` in direction `e_i`.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Definition 2.1, p.4. -/
def lineThrough (u : Fin m → F) (i : Fin m) : Set (Fin m → F) :=
  Set.range fun t : F => u + t • Pi.single i (1 : F)

/-- `u` lies on the line through `u` in any direction (take `t = 0`). -/
theorem self_mem_lineThrough (u : Fin m → F) (i : Fin m) : u ∈ lineThrough u i :=
  ⟨0, by simp⟩

variable (F m) in
/-- An axis-parallel line of `𝔽_q^m`, as a **set of points**.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Definitions 2.1 and
2.4, pp.4–5.

**Formalization Note** A line question is this subtype, never a pair `(u, i)`: the line player must
not learn which point of the line the other player was asked. Two pairs naming the same set name the
same question. -/
def AxisLine : Type _ := {ℓ : Set (Fin m → F) // ∃ u i, ℓ = lineThrough u i}

/-- The line through `u` in direction `e_i`, as a question. -/
def lineOf (u : Fin m → F) (i : Fin m) : AxisLine F m := ⟨lineThrough u i, u, i, rfl⟩

/-- A function `f : ℓ → 𝔽_q` is a **legal answer of degree at most `d`** when, along a
parametrization `t ↦ u + t e_i` of `ℓ`, it is a univariate polynomial of degree at most `d` in `t`.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Definitions 2.1 and
2.4, pp.4–5.

**Formalization Note** Legality does not depend on the chosen parametrization of `ℓ`, since a change
of base point is a translation of `t` (`Solutions/verification/DiagLinesLDT_sanity.lean`). Answers are
functions on `ℓ`, as the source writes them, so `q = 2` gives 4 answers per line, and for `d ≥ q - 1`
every function is legal. -/
def IsLegalAnswer (d : ℕ) (ℓ : AxisLine F m) (f : ℓ.1 → F) : Prop :=
  ∃ (u : Fin m → F) (i : Fin m), ℓ.1 = lineThrough u i ∧
    ∃ p : F[X], p.natDegree ≤ d ∧
      ∀ (t : F) (x : ℓ.1), (x : Fin m → F) = u + t • Pi.single i (1 : F) → f x = p.eval t

/-- The outcome type of a line measurement: the legal answers on `ℓ`. -/
def LegalAnswer (d : ℕ) (ℓ : AxisLine F m) : Type _ := {f : ℓ.1 → F // IsLegalAnswer d ℓ f}

noncomputable instance [Fintype F] (d : ℕ) (ℓ : AxisLine F m) : Fintype (LegalAnswer d ℓ) :=
  have : Finite (ℓ.1 → F) := inferInstance
  have : Finite (LegalAnswer d ℓ) := Subtype.finite
  Fintype.ofFinite _

end DiagLinesLDT


