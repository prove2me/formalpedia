-- Prove2me | Definitions.Def_OnlineSteinitz_Reduction_Supplement_Inputs
-- name    : OnlineSteinitz_Reduction_Supplement_Inputs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:15:29.231581+00:00
-- url     : https://prove2.me/theorems/44f5e163-e288-40ad-8b9f-2c2cf0ec211f
-- title:
--   Zero-sum completions, coordinate cycles and a fixed plane
-- statement:
--   A prefix of $m\le T/2$ unit-ball vectors is completed by $T-m$ copies of minus its total divided by $T-m$. The hard family $I_s$ consists of $s$ cycles of the first $q$ coordinate vectors followed by $T-qs$ copies of $-s\mathbf1_q/(T-qs)$, embedded by zero extension into $\mathbb R^d$. Its domain is $1\le q\le\min(d,\lfloor T/2\rfloor)$ and $1\le s\le\lfloor T/(2q)\rfloor$. All denominators on this domain are positive. The scalar family uses $d=q=1$. The one-cycle family uses $q=\min(d,\lfloor T/2\rfloor)$ and $s=1$.
--
--   The fixed plane is the span of the first two coordinate vectors: every coordinate with zero-based index at least two vanishes. A permutation run places the permuted input at slots $0,\ldots,T-1$ with dummy local histories. It represents every ordering, including offline ones, for the one-cycle result. The completed streams are computed from their initial vectors, rather than supplied as unrelated witnesses.
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; §5.1, (5.1)–(5.2), p.20; Lemma 5.2, pp.20–21; Remark 5.3, p.22

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Algorithms

open scoped BigOperators

namespace OnlineSteinitz.Reduction.Supplement

/-! Zero-sum completion (5.1), p.20; meaningful when xs.length ≤ T/2.
Its repeated vector is calculated from xs, not chosen independently. -/
noncomputable def completeStream {d : ℕ} (T : ℕ) (xs : List (Vec d)) : List (Vec d) :=
  xs ++ List.replicate (T - xs.length)
    (-(1 / ((T - xs.length : ℕ) : ℝ)) • xs.sum)

/-! Equation (5.2), p.20: q coordinates embedded in the first d coordinates.
The domain in each theorem is 1 ≤ q ≤ min(d,T/2), 1 ≤ s ≤ T/(2q).
The modulo fallback at q=0 is never used by these statements. -/
noncomputable def coordinateVector (d j : ℕ) : Vec d :=
  WithLp.toLp 2 (fun i : Fin d => if i.val = j then 1 else 0)

noncomputable def cycleInput (T d q s : ℕ) : Fin T → Vec d :=
  fun t => if t.val < q * s then coordinateVector d (t.val % q)
    else -(s / ((T - q * s : ℕ) : ℝ)) •
      (WithLp.toLp 2 (fun i : Fin d => if i.val < q then 1 else 0) : Vec d)

def ScalarFamily {T : ℕ} (v : Fin T → Vec 1) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ s ≤ T / 2 ∧ v = cycleInput T 1 1 s

def FixedPlane {T d : ℕ} (v : Fin T → Vec d) : Prop :=
  ∀ t (i : Fin d), 2 ≤ i.val → v t i = 0

noncomputable def permutationRun {T d : ℕ} (v : Fin T → Vec d)
    (π : Equiv.Perm (Fin T)) : Run T (Vec d) :=
  ⟨fun _ => [], List.ofFn (fun j : Fin T => (j.val, v (π j)))⟩

end OnlineSteinitz.Reduction.Supplement


