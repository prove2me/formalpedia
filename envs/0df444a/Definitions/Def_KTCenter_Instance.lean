-- Prove2me | Definitions.Def_KTCenter_Instance
-- name    : KTCenter_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:47.358187+00:00
-- url     : https://prove2.me/theorems/e78ddd4f-be1d-44f7-95f3-c279fbc3e140
-- title:
--   Kendall–tau distance $\mathcal K(\sigma,\pi)$, input list, radius $\mathrm{Obj}(\Pi,\sigma)$ and optimal radius $R^*$
-- statement:
--   Let $V=[d]$ be a set of $d$ candidates. A **complete ranking** $\pi$ is a permutation of $V$; candidate $\pi(j)$ occupies position $j$, and the position of $v$ is $\mathrm{pos}_\pi(v)=\pi^{-1}(v)$. The **Kendall–tau distance** counts the unordered pairs ordered differently by two rankings:
--
--   $$\mathcal K(\sigma,\pi)=\Bigl|\Bigl\{\{u,v\}\in\tbinom V2:\ \sigma\text{ and }\pi\text{ order }u,v\text{ differently}\Bigr\}\Bigr|.$$
--
--   An **input** is a list $\Pi=(\pi_1,\dots,\pi_n)$ of $n\ge1$ complete rankings of $d\ge1$ candidates. The **radius** of a ranking $\sigma$ is $\mathrm{Obj}(\Pi,\sigma)=\max_{i\in[n]}\mathcal K(\sigma,\pi_i)$, and the **optimal radius** is $R^*=\min_{\sigma\in S_d}\mathrm{Obj}(\Pi,\sigma)$; a ranking attaining it is an optimal center.
--
--   These are the objects of the Kendall–tau center problem; every statement of the mission is about them.
--
--   **Formalization Note** A ranking is `Equiv.Perm (Fin d)` read in one-line form, so candidate labels and positions are 0-based in Lean. An unordered pair $\{u,v\}$ is the ordered pair $(u,v)$ with $u<v$. The input is a list (`Fin n → Equiv.Perm (Fin d)`), which allows repeated rankings and covers every set. The maximum and minimum are taken over nonempty finite sets.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), eq. (1) and "Distance metric", p.13 (PDF p.15); Theorem 1.1, p.2 (PDF p.4)

import Mathlib

namespace KTCenter

/-- **Kendall–tau distance**, eq. (1), p.13 (PDF p.15).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…), §3, p.13: `𝒦(σ, π)` is the number of unordered candidate pairs on which `σ` and
`π` disagree.

**Formalization Note.** A ranking is `Equiv.Perm (Fin d)`, read in one-line form as on p.13:
`π j` is the candidate at position `j`, so the position of `v` is `π⁻¹ v`, and `u ≺_π v` is
`π⁻¹ u < π⁻¹ v`. An unordered pair `{u, v}` is the ordered pair `(u, v)` with `u < v`. -/
def dist {d : ℕ} (σ π : Equiv.Perm (Fin d)) : ℕ :=
  (Finset.univ.filter fun p : Fin d × Fin d =>
    p.1 < p.2 ∧ ¬ (σ⁻¹ p.1 < σ⁻¹ p.2 ↔ π⁻¹ p.1 < π⁻¹ p.2)).card

/-- **An input of the Kendall–tau center problem**, Theorem 1.1, p.2 and §3, p.13: a list
`Π = (π₁, …, πₙ)` of `n ≥ 1` complete rankings of `d ≥ 1` candidates.

**Formalization Note.** The paper writes "a set Π" on p.2 and "the input list" on p.13. Lean takes
the list, `Fin n → Equiv.Perm (Fin d)`, which covers every set and allows repeats, as Algorithm 10
does. The source's input `π₁` is `π ⟨0, _⟩`. -/
structure Instance where
  /-- the number of input rankings -/
  n : ℕ
  /-- the number of candidates -/
  d : ℕ
  one_le_n : 1 ≤ n
  one_le_d : 1 ≤ d
  /-- the input rankings -/
  π : Fin n → Equiv.Perm (Fin d)

namespace Instance

instance (I : Instance) : Nonempty (Fin I.n) := ⟨⟨0, I.one_le_n⟩⟩

/-- The source's first input index `1`, which is `⟨0, _⟩` in `Fin n`. -/
def first (I : Instance) : Fin I.n := ⟨0, I.one_le_n⟩

end Instance

/-- **Radius** `Obj(Π, σ) = max_{i∈[n]} 𝒦(σ, πᵢ)`, p.13 (PDF p.15). -/
def obj (I : Instance) (σ : Equiv.Perm (Fin I.d)) : ℕ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => dist σ (I.π i)

/-- **Optimal radius** `R* = min_{σ∈S_d} Obj(Π, σ)`, p.13 (PDF p.15). -/
def optRadius (I : Instance) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty fun σ => obj I σ

end KTCenter


