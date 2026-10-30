-- Prove2me | Definitions.Def_KUMultimodular_multimodular
-- name    : KUMultimodular_multimodular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:58:25.23765+00:00
-- url     : https://prove2.me/theorems/f978b825-9279-49bc-bccd-2100a67c109a
-- title:
--   Algorithm MULTIMODULAR over $\mathbb Z/r\mathbb Z$
-- statement:
--   Let $r \ge 1$, $t \ge 1$, $f \in (\mathbb Z/r\mathbb Z)[X_0,\dots,X_{m-1}]$ with degree at most $d-1$ in each variable, and $\alpha_0,\dots,\alpha_{N-1} \in (\mathbb Z/r\mathbb Z)^m$. **Algorithm MULTIMODULAR** with $t$ rounds:
--
--   1. Lift every coefficient of $f$ and every coordinate of every $\alpha_i$ to $\{0,\dots,r-1\}$, giving $\tilde f \in \mathbb Z[X_0,\dots,X_{m-1}]$ and $\tilde\alpha_i \in \mathbb Z^m$.
--   2. Compute the primes $p_1,\dots,p_k \le \ell$, where
--   $$\ell = \bigl\lfloor 16 \ln \max\bigl(2,\ d^m (r-1)^{md}\bigr) \bigr\rfloor .$$
--   3. Reduce $\tilde f$ and every $\tilde\alpha_i$ modulo every $p_h$ (one remainder tree per coefficient and per coordinate), giving $f_h \in \mathbb F_{p_h}[X]$ and $\alpha_{h,i} \in \mathbb F_{p_h}^m$.
--   4. If $t = 1$, compute $f_h(\alpha_{h,i})$ with the algorithm of Theorem 4.1 for every $h$; if $t > 1$, run MULTIMODULAR over $\mathbb Z/p_h\mathbb Z$ with $t-1$ rounds for every $h$.
--   5. For every $i$, compute by Chinese remaindering the unique integer in $\{0,\dots,p_1\cdots p_k - 1\}$ congruent to $f_h(\alpha_{h,i})$ modulo $p_h$ for all $h$, and return it modulo $r$.
--
--   The number $\ell$ is chosen so that $p_1 \cdots p_k$ exceeds every value $\tilde f(\tilde\alpha_i)$ (Lemma 2.4), which makes the Chinese remaindering exact. Recursing $t$ times shrinks the moduli from $r$ to about $\log^{(t)} r$, which is what removes the poor dependence on $p$ in Theorem 4.1.
--
--   **Formalization Note** `multimodular t r m d N c α : Timed (Fin N → ZMod r)`; the lift is `ZMod.val`. Steps 2–5 are `mmCore ellC`, which works on lists of lifts and takes the computation of $\ell$ as a parameter only so that the verification file can run it with a computable $\ell$. The paper's $\ell = 16\log(d^m(r-1)^{md})$ is clipped at argument $2$: when $d^m(r-1)^{md} \le 1$ the printed $\ell$ is $\le 0$, there are no primes, and the algorithm would return $0$ (for $r = 2$, $m = d = 1$, $f = 1$); for $d^m(r-1)^{md} \ge 2$ it is the printed $\ell$ with the natural logarithm. For $t = 0$ the definition behaves as for $t = 1$; the paper requires $t \ge 1$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), §4.2, Algorithm MULTIMODULAR, p. 12

import Mathlib
import Definitions.Def_KUMultimodular_Timed
import Definitions.Def_KUMultimodular_densePoly
import Definitions.Def_KUMultimodular_fpEval

namespace KUMultimodular

/-! # Algorithm MULTIMODULAR (Kedlaya–Umans, Dagstuhl Seminar Proceedings 08381 (2008), §4.2, p. 12)

Coefficients and coordinates are carried as their lifts in `{0, …, r-1}`; the polynomial is a dense
list in lexicographic order and every point a list of `m` coordinates. -/

/-- **The prime bound `ℓ`** of Step 2: `ℓ = ⌊16 log (max 2 (d^m (r-1)^{md}))⌋` (natural logarithm).
The paper's `ℓ = 16 log(d^m (r-1)^{md})` is used with the argument clipped at `2`: for
`d^m (r-1)^{md} ≤ 1` the printed `ℓ` is `≤ 0`, there are no primes, and the algorithm would return
`0` (e.g. `r = 2`, `m = d = 1`, `f = 1`), so the clipping is a correction. For
`d^m (r-1)^{md} ≥ 2` it is the printed value. -/
noncomputable def ellValue (d m r : ℕ) : ℕ :=
  ⌊16 * Real.log (max 2 (((d ^ m * (r - 1) ^ (m * d) : ℕ)) : ℝ))⌋₊

/-- Computing `ℓ` (Step 2), charged `ql` of the bit size of `d^m (r-1)^{md}` plus one. -/
noncomputable def ellC (d m r : ℕ) : Timed ℕ :=
  ⟨ellValue d m r, ql (m * d * (bits r + bits d) + 1)⟩

/-- **Algorithm MULTIMODULAR on lifted dense lists**, with the computation of `ℓ` passed as
`ellF` (the algorithm proper is `mmCore ellC`; the parameter only lets the verification file run
it with a computable `ℓ`). `mmCore ellF m d n r cs pts` runs `t = n + 1` rounds over `ℤ/rℤ`;
`cs` lists the lifts of the `d^m` coefficients, `pts` the lifts of the points. Returns the lifts
of the values. -/
def mmCore (ellF : ℕ → ℕ → ℕ → Timed ℕ) (m d : ℕ) :
    ℕ → ℕ → List ℕ → List (List ℕ) → Timed (List ℕ)
  | n, r, cs, pts => do
    -- Step 1: the lifts (read once)
    tick (lsize cs + (pts.map lsize).sum + 1)
    -- Step 2: the primes `p_1, …, p_k ≤ ℓ`
    let ell ← ellF d m r
    let ps ← primesUpToC ell
    -- Step 3: reductions modulo every `p_h` (one remainder tree per coefficient / coordinate)
    let csRes ← mapT (fun c => remTreeC c ps) cs
    let ptRes ← mapT (fun a => mapT (fun x => remTreeC x ps) a) pts
    let csP ← regroupT bits ps.length 0 csRes
    let ptT ← mapT (fun a => regroupT bits ps.length 0 a) ptRes
    let ptP ← regroupT lsize ps.length [] ptT
    -- Step 4: evaluate modulo every `p_h`
    let results ← mapT (fun q : ℕ × (List ℕ × List (List ℕ)) =>
        match n with
        | 0 => do
            -- `t = 1`: the algorithm of Theorem 4.1 over `𝔽_{p_h}`
            let cZ ← mapT (fun x : ℕ => pure (x : ZMod q.1)) q.2.1
            let pZ ← mapT (fun a : List ℕ => mapT (fun x : ℕ => pure (x : ZMod q.1)) a) q.2.2
            let out ← fpEvalL q.1 m d cZ pZ
            mapT (fun v => pure v.val) out
        | n' + 1 =>
            -- `t > 1`: MULTIMODULAR over `ℤ/p_hℤ` with `t - 1` rounds
            mmCore ellF m d n' q.1 q.2.1 q.2.2)
      (List.zip ps (List.zip csP ptP))
    -- Step 5: Chinese remaindering, then reduction modulo `r`
    let perPoint ← regroupT bits pts.length 0 results
    mapT (fun res => do
        let y ← crtC res ps
        let qr ← divModC y r
        pure qr.2) perPoint

/-- **Algorithm MULTIMODULAR(f, α_0, …, α_{N-1}, r, t)** (Kedlaya–Umans 2008, §4.2, p. 12), on the
paper's input: the coefficient table `c` of `f ∈ (ℤ/rℤ)[X_0, …, X_{m-1}]` with degree at most
`d - 1` in each variable, the points `α_0, …, α_{N-1} ∈ (ℤ/rℤ)^m`, and the number of rounds
`t ≥ 1`. Step 1 lifts every coefficient and coordinate to `{0, …, r-1}` (`ZMod.val`); then
`mmCore ellC` performs Steps 2–5 with `t` rounds, calling the algorithm of Theorem 4.1 (`fpEvalL`)
at the last round. (For `t = 0` it behaves as for `t = 1`; the paper requires `t ≥ 1`.) -/
noncomputable def multimodular (t r m d N : ℕ) (c : (Fin m → Fin d) → ZMod r)
    (α : Fin N → Fin m → ZMod r) : Timed (Fin N → ZMod r) := do
  let cs ← mapT (fun a => do tick (bits (c a).val); pure (c a).val) (lexEnum d m)
  let pts ← mapT (fun i => mapT (fun j => do tick (bits (α i j).val); pure (α i j).val)
    (List.finRange m)) (List.finRange N)
  let out ← mmCore ellC m d (t - 1) r cs pts
  pure (fun i => ((out.getD i 0 : ℕ) : ZMod r))

end KUMultimodular


