-- Prove2me | Definitions.Def_ExactPatternStream_LinearMaps
-- name    : ExactPatternStream_LinearMaps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:12.221391+00:00
-- url     : https://prove2.me/theorems/b5ecc828-cc63-4719-ad3d-2f60cb7a7d3b
-- title:
--   §6, (13), Definition 7.2 — $\Delta_p$, $D_v$, $M_{a,b}$, $M^{(d)}_{a,b}$, $R_s$
-- statement:
--   For a vector string $T$ over a field $F$ and $1\le p<|T|$, $\Delta_p(T)=\mathrm{span}\{T[i+p]-T[i]:0\le i<|T|-p\}$. For strings $P,T$, $D_v=\mathrm{span}\{T[v+t]-P[t]:0\le t<m\}$.
--
--   $M_{a,b}:F^3\to F^2$ is $M_{a,b}(x_1,x_2,x_3)=(x_1+ax_3,x_2+bx_3)$. $M^{(d)}_{a,b}:F^d\to F^{\lceil2d/3\rceil}$ applies $M_{a,b}$ to every consecutive triple and leaves the final $d\bmod3$ coordinates unchanged. With $d_0=d$, $d_{r+1}=\lceil2d_r/3\rceil$ and $D$ the least index with $d_D=2$, for a seed $s=((a_0,b_0),\dots,(a_{D-1},b_{D-1}))$,
--   $$R_s=M^{(d_{D-1})}_{a_{D-1},b_{D-1}}\circ\dots\circ M^{(d_0)}_{a_0,b_0}.$$
--   These recursive random linear maps are the paper's new fingerprint: short seed, small working space, and a failure bound with no union over positions.
--
--   **Formalization Note** $M^{(d)}$ acts on the list of coordinates. $D$ is an infimum in `ℕ`; every use has $d\ge3$, where it is attained.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), §6, p.15 (PDF 16), Lemma 6.2, p.16 (PDF 17), eq. (13), p.17 (PDF 18), Definition 7.2, p.18 (PDF 19)

import Mathlib

namespace ExactPatternStream

/-! # Vector strings and recursive random linear maps

Gawrychowski, Janczewski, Jin, Nelson (preprint, sha256 351218cb…), §6, p.15 (PDF 16), Lemma 6.2's `D_v`,
p.16 (PDF 17), eq. (13), p.17 (PDF 18), and Definition 7.2, p.18 (PDF 19).

**Formalization Note.** A vector string is `Fin n → V`. `M^{(d)}` acts on the list of coordinates: it maps
each consecutive triple by `M_{a,b}` and leaves the final `d mod 3` coordinates unchanged, so its output
has length `⌈2d/3⌉`. `roundsD d` is the least `D` with `d_D = 2` (an infimum in `ℕ`), and the set is nonempty
exactly when `d ≥ 2`; every use has `d ≥ 3`. -/

section Spans

variable (F : Type*) {V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- `Δ_p(T) = span{T[i + p] - T[i] : 0 ≤ i < |T| - p}`, p.15. -/
def deltaSpan {n : ℕ} (T : Fin n → V) (p : ℕ) : Submodule F V :=
  Submodule.span F {x | ∃ (i : ℕ) (h : i + p < n), x = T ⟨i + p, h⟩ - T ⟨i, by omega⟩}

/-- `D_v = span{T[v + t] - P[t] : 0 ≤ t < m}`, Lemma 6.2. -/
def mismatchSpan {m n : ℕ} (P : Fin m → V) (T : Fin n → V) (v : ℕ) : Submodule F V :=
  Submodule.span F {x | ∃ (t : ℕ) (ht : t < m) (h : v + t < n), x = T ⟨v + t, h⟩ - P ⟨t, ht⟩}

end Spans

section Maps

variable {F : Type*} [Field F]

/-- `M_{a,b}(x₁, x₂, x₃) = (x₁ + a x₃, x₂ + b x₃)`, eq. (13). -/
def mab (a b : F) (x : Fin 3 → F) : Fin 2 → F := ![x 0 + a * x 2, x 1 + b * x 2]

/-- `M^{(d)}_{a,b}`: `M_{a,b}` on every consecutive triple, the final `d mod 3` coordinates unchanged. -/
def mabD (a b : F) : List F → List F
  | x₁ :: x₂ :: x₃ :: rest => (x₁ + a * x₃) :: (x₂ + b * x₃) :: mabD a b rest
  | xs => xs

/-- `d_{r+1} = ⌈2 d_r / 3⌉`, Definition 7.2. -/
def dNext (d : ℕ) : ℕ := (2 * d + 2) / 3

/-- `D`, the least index such that `d_D = 2`, Definition 7.2. -/
noncomputable def roundsD (d : ℕ) : ℕ := sInf {r | dNext^[r] d = 2}

/-- Apply the rounds of `R_s` in order, for a list of seed pairs. -/
def applyRounds (s : List (F × F)) (x : List F) : List F :=
  s.foldl (fun y p => mabD p.1 p.2 y) x

/-- `R_s = M^{(d_{D-1})}_{a_{D-1},b_{D-1}} ∘ ⋯ ∘ M^{(d_0)}_{a_0,b_0}`, Definition 7.2. -/
noncomputable def rs {d : ℕ} (s : Fin (roundsD d) → F × F) (x : Fin d → F) : List F :=
  applyRounds (List.ofFn s) (List.ofFn x)

end Maps

end ExactPatternStream


