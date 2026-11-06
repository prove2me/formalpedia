-- Prove2me | Definitions.Def_StrongConvPuder
-- name    : StrongConvPuder
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T20:42:39.889208+00:00
-- url     : https://prove2.me/theorems/e4ea6657-a220-4035-ba5f-c995825c7207
-- title:
--   Primitivity rank π(w) and critical subgroups Crit(w) (Puder), and the coefficients b_s(w) of N·E[tr_N w(Sᴺ)]
-- statement:
--   Definitions for the two results of Puder cited in the proof of Lemma 8.5 of Chen–Garza-Vargas–Tropp–van Handel, *A new approach to strong convergence* (pp. 25–26). Here $\mathbf F_d$ is `FreeGroup (Fin d)`.
--
--   - `Puder.IsPrimitiveIn J w`: the element $w$ is *primitive* in the subgroup $J \le \mathbf F_d$, that is, $w$ belongs to a basis (free generating set) of $J$, written as a `FreeGroupBasis` of $J$ indexed by some type. Puder, p. 8: “A word $w \in \mathbf F_k$ is *primitive* if it belongs to a *basis* of $\mathbf F_k$. For a given $w$, one can also ask whether $w$ is primitive as an element of different subgroups of $\mathbf F_k$ (which are free as well by a classical theorem of Nielsen and Schreier …)”, with the footnote “A basis of a free group is a free generating set.”
--   - `Puder.HasRank J r`: $J$ has a basis indexed by $\{0, \dots, r-1\}$, so it is free of rank $r$. Puder, p. 8, footnote: “The *rank* of a free group $\mathbf F$, denoted $\mathrm{rk}(\mathbf F)$, is the size of (every) basis of $\mathbf F$.”
--   - `Puder.primitivityRank w` $= \pi(w) \in \mathbb N \cup \{\infty\}$: the least $r$ such that some $J \le \mathbf F_d$ of rank $r$ contains $w$ and $w$ is not primitive in $J$; it is $\infty$ (`⊤ : ℕ∞`) if there is no such $J$ of finite rank. Puder, Definition 2.2 (p. 9): “The *primitivity rank* of $w \in \mathbf F_k$, denoted $\pi(w)$, is $$\pi(w) = \min\Big\{\mathrm{rk}(J) \;\Big|\; \begin{matrix} w \in J \le \mathbf F_k \textit{ s.t.} \\ w \text{ is } \textbf{not} \text{ primitive in } J \end{matrix}\Big\}.$$ If no such $J$ exists, i.e. if $w$ is primitive in $\mathbf F_k$, then $\pi(w) = \infty$.” Only $J$ of finite rank are counted. This gives Puder's value: a finite minimum is attained by a $J$ of finite rank, and when only subgroups of infinite rank witness non-primitivity, the minimum is $\infty$ in both readings.
--   - `Puder.Crit w`: the set of $w$-critical subgroups, the $J \le \mathbf F_d$ of finite rank containing $w$, in which $w$ is not primitive, and whose rank equals $\pi(w)$. Puder, p. 9: “A subgroup $J$ for which the minimum is obtained is called *$w$-critical*, and the set of $w$-critical subgroups is denoted $\mathrm{Crit}(w)$.” Here it is empty when $\pi(w) = \infty$. In Puder's reading it is empty then too, because $\pi(w) = \infty$ only for $w$ primitive in $\mathbf F_k$, and such $w$ is primitive in every subgroup containing it (p. 8, citing Puder, Israel J. Math. 201 (2014), Claim 2.5). Its size $|\mathrm{Crit}(w)|$ is written with `Set.ncard`, which is $0$ for an infinite set; it is always finite, by the theorem of Puder–Parzanchevski quoted on Puder's p. 9 (“In particular, it is also shown that $\mathrm{Crit}(w)$ is always finite.”).
--   - `StrongConv.wordCoeff w s` $= b_s(w)$, for a word $w$ in the letters $g_0 = e, g_1, \dots, g_{2d}$ (`List (StrongConv.Letter d)`): the $s$-th coefficient (`StrongConv.asympCoeff`) of the expansion of $N\,\mathbf E[\mathrm{tr}_N\, w(\boldsymbol S^N)]$ in powers of $1/N$, where $\boldsymbol S^N$ is the $d$-tuple of independent uniformly random $N \times N$ permutation matrices restricted to $\{1_N\}^\perp$ and $\mathrm{tr}_N$ is the trace divided by $N$. CGTvH, pp. 25–26: “Fix a word $w \in \mathbf W_d$ of length $q$ that does not reduce to the identity. By Lemmas 5.1 and 5.2, we can write for all sufficiently large $N$ $$N\,\mathbf E[\mathrm{tr}_N\, w(\boldsymbol S^N)] = \sum_{s=0}^\infty \frac{b_s(w)}{N^s},$$ as a rational function is analytic away from its poles.”
--
--   Sources: D. Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216, §2, p. 9); C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, pp. 25–26).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 26, the primitivity rank π(w), Crit(w) and the coefficients b_s(w) in the proof of Lemma 8.5, which refers to Puder, D., Expansion of random graphs: new proofs, new results, Invent. Math. 201 (2015) 845–908, https://doi.org/10.1007/s00222-014-0560-x (arXiv:1212.5216), §2.2, Definition 2.2

import Mathlib
import Definitions.Def_StrongConv

/-!
# Primitivity rank and critical subgroups (Puder), and the coefficients `b_s(w)` (CGTvH)

Puder, *Expansion of random graphs: new proofs, new results*, Invent. Math. 201 (2015), §2,
Definition 2.2; Chen–Garza-Vargas–Tropp–van Handel, *A new approach to strong convergence*,
proof of Lemma 8.5 (arXiv:2405.16026v3, p. 25).
-/

namespace Puder

/-- `w` is primitive in the subgroup `J` of `F_d`: `w` is an element of some basis (free
generating set) of `J`. -/
def IsPrimitiveIn {d : ℕ} (J : Subgroup (FreeGroup (Fin d))) (w : FreeGroup (Fin d)) : Prop :=
  ∃ (ι : Type) (b : FreeGroupBasis ι J) (i : ι), (b i : FreeGroup (Fin d)) = w

/-- `J` is a free group of rank `r`: it has a basis with `r` elements. -/
def HasRank {d : ℕ} (J : Subgroup (FreeGroup (Fin d))) (r : ℕ) : Prop :=
  Nonempty (FreeGroupBasis (Fin r) J)

/-- Puder, Definition 2.2: the primitivity rank `π(w)`, the least rank of a subgroup `J ≤ F_d`
containing `w` in which `w` is not primitive, and `∞` if there is none. -/
noncomputable def primitivityRank {d : ℕ} (w : FreeGroup (Fin d)) : ℕ∞ :=
  ⨅ (r : ℕ) (_ : ∃ J : Subgroup (FreeGroup (Fin d)), w ∈ J ∧ HasRank J r ∧ ¬ IsPrimitiveIn J w),
    (r : ℕ∞)

/-- Puder, Definition 2.2: `Crit(w)`, the `w`-critical subgroups: the subgroups `J ≤ F_d`
containing `w`, in which `w` is not primitive, whose rank is `π(w)`. -/
def Crit {d : ℕ} (w : FreeGroup (Fin d)) : Set (Subgroup (FreeGroup (Fin d))) :=
  {J | w ∈ J ∧ ¬ IsPrimitiveIn J w ∧ ∃ r : ℕ, HasRank J r ∧ (r : ℕ∞) = primitivityRank w}

end Puder

namespace StrongConv

/-- CGTvH p. 25: `b_s(w)`, the `s`-th coefficient of the expansion
`N E[tr_N w(Sᴺ)] = ∑_s b_s(w) / Nˢ` in powers of `1/N`. -/
noncomputable def wordCoeff {d : ℕ} (w : List (Letter d)) (s : ℕ) : ℝ :=
  asympCoeff (fun N : ℕ => (N : ℝ) * uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
    trN N (wordEval (sModel σ) w))) s

end StrongConv


