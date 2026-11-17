-- Prove2me | Definitions.Def_OnlineCAP_Supplement_algorithm1
-- name    : OnlineCAP_Supplement_algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:19:45.119745+00:00
-- url     : https://prove2.me/theorems/8a12bcb3-b2df-4e7d-9bf8-0c5fccc0e162
-- title:
--   Algorithm 1 (OCycAP under cut arrivals)
-- statement:
--   **Algorithm 1** solves unweighted online cycle augmentation with cut arrivals using two rectangle-hitting subroutines. Its input is the number $n$ of vertices of the cycle $v_0v_1\cdots v_{n-1}v_0$, a set $L$ of links, and subroutine families $A_L$ (for leftless rectangles) and $A_T$ (for topless rectangles), which are run with grid size $N=n$ on the point set $P=\{p_\ell:\ell\in L\}$, $p_\ell=(i,j)$ for $\ell=\{v_i,v_j\}$, $i<j$.
--
--   It keeps a link set $F$, initially empty. When a cut $C=[a,b]$ arrives:
--
--   1. if some link of $F$ crosses $C$, nothing is done;
--   2. otherwise the leftless rectangle $R_L(a,b)=(-\infty,a-1]\times[a,b]$ is fed to $A_L$ and the topless rectangle $R_T(a,b)=[a,b]\times[b+1,\infty)$ to $A_T$, and $F$ becomes the set of links $\ell\in L$ whose point $p_\ell$ has been bought by $A_L$ or by $A_T$.
--
--   The algorithm is deterministic and online: after the cuts $C_1,\dots,C_t$ its link set depends only on these cuts.
--
--   **Formalization Note** It is a randomized online algorithm on a one-point coin space. Because the subroutines never discard points, recomputing $F$ from all purchased points is the same as adding the new links in each step. The subroutines are deterministic in Theorem 3.3; one fixed outcome of their coins is used.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Algorithm 1, p.12 (PDF p.12); §3.1, p.11

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_RL
import Definitions.Def_OnlineCAP_RT
import Definitions.Def_OnlineCAP_linkPoint
import Definitions.Def_OnlineCAP_Supplement_cutArc

open MeasureTheory

namespace OnlineCAP.Supplement

/-- A fixed outcome of the coins of an online algorithm (its sample space is nonempty, since it
carries a probability measure). Used to run a deterministic subroutine. -/
noncomputable def someOutcome {U Req : Type} (A : RandOnlineAlg U Req) : A.Ω :=
  Classical.choice (nonempty_of_isProbabilityMeasure A.μ)

/-- The links of Algorithm 1 after the subroutines have been fed the lists `σ = (σ_L, σ_T)`: the
links `ℓ ∈ L` whose point `p_ℓ` has been bought by `A_L` or by `A_T` (line 12 of Algorithm 1). -/
noncomputable def alg1Links (AL AT : ℕ → Finset (ℝ × ℝ) → RandOnlineAlg (ℝ × ℝ) (Set (ℝ × ℝ)))
    (n : ℕ) (L : Finset (Sym2 (Fin n))) (σ : List (Set (ℝ × ℝ)) × List (Set (ℝ × ℝ))) :
    Finset (Sym2 (Fin n)) := by
  classical
  exact L.filter (fun ℓ => linkPoint ℓ ∈
    (AL n (linkPoints L)).buy (someOutcome (AL n (linkPoints L))) σ.1 ∪
      (AT n (linkPoints L)).buy (someOutcome (AT n (linkPoints L))) σ.2)

/-- One arrival in Algorithm 1 (lines 6–12): if the cut `C = [a, b]` is crossed by a current
link, nothing changes; otherwise `R_L(a, b)` is appended to the list fed to `A_L` and `R_T(a, b)`
to the list fed to `A_T`. -/
noncomputable def alg1Step (AL AT : ℕ → Finset (ℝ × ℝ) → RandOnlineAlg (ℝ × ℝ) (Set (ℝ × ℝ)))
    (n : ℕ) (L : Finset (Sym2 (Fin n))) (σ : List (Set (ℝ × ℝ)) × List (Set (ℝ × ℝ)))
    (C : Finset (Fin n)) : List (Set (ℝ × ℝ)) × List (Set (ℝ × ℝ)) := by
  classical
  exact if ∃ ℓ ∈ alg1Links AL AT n L σ, crosses ℓ C then σ
    else (σ.1 ++ [RL (cutArc C).1 (cutArc C).2], σ.2 ++ [RT (cutArc C).1 (cutArc C).2])

/-- **Algorithm 1 (OCycAP under cut arrivals).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and
Unweighted Online Connectivity Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026
(sha256 e3b9cb64…), Algorithm 1, p.12 (PDF p.12): "2 Let P = {(i, j) : (vi, vj) ∈ L, i < j} ⊆
[0, n)² ∩ Z². 3 Initialize F ← ∅. 4 Initialize a leftless-rectangle hitting-set algorithm AL on P
5 Initialize a topless-rectangle hitting-set algorithm AT on P. 6 For each arriving cut C = [a, b]:
7 If C is already covered by F, do nothing. 8 If C is not covered by F: 9 Let RL = (−∞, a − 1] ×
[a, b] and RT = [a, b] × [b + 1, ∞). 10 Feed the leftless rectangle RL to the algorithm AL and let
QL be the set of points purchased. 11 Feed the topless rectangle RT to the algorithm AT and let QT
be the set of points purchased. 12 Add to F the links corresponding to points in QL ∪ QT."

Given subroutine families `A_L`, `A_T` (run with `N = n` on `P = P_L`), the number of vertices `n`
and the links `L`, the state after the cuts `s` is `s.foldl alg1Step ([], [])`, and the purchased
set is `F = {ℓ ∈ L : p_ℓ ∈ Q_L ∪ Q_T}`.

**Formalization Note.** A deterministic algorithm on the one-point coin space `Unit`. Since the
subroutines' purchases only grow, recomputing `F` from `Q_L ∪ Q_T` equals adding the new links at
each step. The cut `C` is turned into `[a, b]` by `cutArc` (the side not containing `v₀`). A
request that is not a 2-cut of the cycle never occurs in a valid sequence; it is processed by the
same rule. The subroutines are deterministic in Theorem 3.3; `someOutcome` fixes one coin outcome
of each. -/
noncomputable def algorithm1 (AL AT : ℕ → Finset (ℝ × ℝ) → RandOnlineAlg (ℝ × ℝ) (Set (ℝ × ℝ)))
    (n : ℕ) (L : Finset (Sym2 (Fin n))) : RandOnlineAlg (Sym2 (Fin n)) (Finset (Fin n)) where
  Ω := Unit
  μ := Measure.dirac ()
  buy := fun _ s => alg1Links AL AT n L (s.foldl (alg1Step AL AT n L) ([], []))
  init := by
    intro ω
    classical
    simp [alg1Links, RandOnlineAlg.init]
  mono := by
    intro ω s r
    classical
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize s.foldl (alg1Step AL AT n L) ([], []) = σ
    unfold alg1Step
    split_ifs
    · exact le_refl _
    · intro ℓ hℓ
      simp only [alg1Links, Finset.mem_filter, Finset.mem_union] at hℓ ⊢
      refine ⟨hℓ.1, ?_⟩
      rcases hℓ.2 with h | h
      · exact Or.inl ((AL n (linkPoints L)).mono _ _ _ h)
      · exact Or.inr ((AT n (linkPoints L)).mono _ _ _ h)
  meas := fun _ _ => Subsingleton.measurableSet

end OnlineCAP.Supplement


