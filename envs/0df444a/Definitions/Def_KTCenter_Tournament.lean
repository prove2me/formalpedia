-- Prove2me | Definitions.Def_KTCenter_Tournament
-- name    : KTCenter_Tournament
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:49.865329+00:00
-- url     : https://prove2.me/theorems/82028b5e-f4ab-4377-a498-db3faa4f3209
-- title:
--   Tournaments, the ordering cost $c_T$, and the tournament of §4.3
-- statement:
--   A **tournament** $T$ on the candidates contains exactly one of the arcs $u\to v$ and $v\to u$ for each pair $\{u,v\}$. The **ordering cost** of a ranking $\omega$ counts the arcs pointing backwards in it:
--
--   $$c_T(\omega)=\bigl|\{u\to v\in T:\ v\prec_\omega u\}\bigr|.$$
--
--   Given a set $E$ of pairs and a ranking $\sigma$, the tournament of §4.3 orders each pair of $E$ as $\sigma$ does and every other pair as the reference $\rho=(1,\dots,d)$. It may contain directed cycles (Figure 3).
--
--   Minimum-cost orderings of this tournament are the near-optimal rankings with bounded movement of Section 4.
--
--   **Formalization Note** Arcs are a Boolean relation with no loops. A pair $\{u,v\}$ is looked up in $E$ as $(\min(u,v),\max(u,v))$.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), §3 p.14 (PDF p.16), §4.3 p.18 (PDF p.20)

import Mathlib

namespace KTCenter

/-- **Tournament**, p.14 (PDF p.16): "T contains exactly one of the arcs u → v and v → u for each
pair {u, v}".

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…). -/
structure Tournament (d : ℕ) where
  /-- `arc u v = true` says that `u → v` is in `T` -/
  arc : Fin d → Fin d → Bool
  arc_self : ∀ v, arc v v = false
  arc_exactly_one : ∀ u v, u ≠ v → (arc u v = true ↔ arc v u = false)

/-- **Ordering cost**, p.14: `c_T(ω) = |{u → v ∈ T : v ≺_ω u}|`. -/
def Tournament.cost {d : ℕ} (T : Tournament d) (ω : Equiv.Perm (Fin d)) : ℕ :=
  (Finset.univ.filter fun p : Fin d × Fin d => T.arc p.1 p.2 = true ∧ ω⁻¹ p.2 < ω⁻¹ p.1).card

/-- **The tournament of §4.3**, p.18 (PDF p.20): each pair of `E` is ordered as in `σ*` and every
other pair as in `ρ = (1, …, d)`.

**Formalization Note.** `E` is a set of pairs `(u, v)` with `u < v`; the pair `{u, v}` is looked up
as `(min u v, max u v)`. -/
def centerTournament {d : ℕ} (E : Finset (Fin d × Fin d)) (σ : Equiv.Perm (Fin d)) :
    Tournament d where
  arc u v := decide (u ≠ v ∧
    (((min u v, max u v) ∈ E ∧ σ⁻¹ u < σ⁻¹ v) ∨ ((min u v, max u v) ∉ E ∧ u < v)))
  arc_self v := by simp
  arc_exactly_one u v h := by
    have h1 : σ⁻¹ u ≠ σ⁻¹ v := fun e => h (σ⁻¹.injective e)
    have hvu : v ≠ u := fun e => h e.symm
    rw [min_comm v u, max_comm v u]
    by_cases hE : (min u v, max u v) ∈ E
    · simp only [hE, h, hvu, decide_eq_true_eq, decide_eq_false_iff_not, ne_eq, not_false_eq_true,
        true_and, not_true_eq_false, false_and, or_false, not_lt]
      exact ⟨fun h2 => h2.le, fun h2 => lt_of_le_of_ne h2 h1⟩
    · simp only [hE, h, hvu, decide_eq_true_eq, decide_eq_false_iff_not, ne_eq, not_false_eq_true,
        true_and, false_and, false_or, not_lt]
      exact ⟨fun h2 => h2.le, fun h2 => lt_of_le_of_ne h2 h⟩

end KTCenter


