-- Prove2me | Definitions.Def_FourierSparseTesting1656_Uniform_Correction
-- name    : FourierSparseTesting1656_Uniform_Correction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:32.472266+00:00
-- url     : https://prove2.me/theorems/2315367d-679f-4340-9fc2-280a56f3ba35
-- title:
--   The checks of SpectrumTest, the rejection probability $p_H(f)$, votes and corrected spectra
-- statement:
--   Fix an integer $s$, a subspace $H\le\mathbb F_2^n$, a complement $W$ of $H^\perp$ and a Boolean $f$. For shifts $a,r$, the checks of Algorithm 1 (SpectrumTest) on the four restrictions at $0,a,r,a+r$ are:
--
--   1. *Sparsity:* each of $\hat f_H,\hat f_{a+H},\hat f_{r+H},\hat f_{a+r+H}$ has at most $s$ nonzero coefficients.
--   2. *Magnitude:* $|\hat f_{a+H}(\gamma)|=|\hat f_{r+H}(\gamma)|=|\hat f_{a+r+H}(\gamma)|=|\hat f_H(\gamma)|$ for every $\gamma\in W$.
--   3. *Triangle:* for every $\gamma\in\operatorname{supp}(\hat f_H)$,
--   $$\frac{\hat f_{a+H}(\gamma)}{\hat f_H(\gamma)}\cdot\frac{\hat f_{r+H}(\gamma)}{\hat f_H(\gamma)}=\frac{\hat f_{a+r+H}(\gamma)}{\hat f_H(\gamma)}.$$
--   4. *Additive:* for all $\gamma_1,\gamma_2,\gamma_3,\gamma_4\in\operatorname{supp}(\hat f_H)$ with $\gamma_1+\gamma_2=\gamma_3+\gamma_4$, the products of the ratios $\hat f_{a+H}(\gamma_i)/\hat f_H(\gamma_i)$ over $\{1,2\}$ and over $\{3,4\}$ agree.
--
--   The rejection probability $p_H(f)$ is the probability, over independent uniform $a,r\in\mathbb F_2^n$ with $H$ and $W$ fixed, that some check fails. The vote of $r$ for the coset $a+H$ is the vector
--   $$\hat\phi^r_{a+H}(\gamma)=\begin{cases}\hat f_{a+r+H}(\gamma)\hat f_{r+H}(\gamma)/\hat f_H(\gamma),&\gamma\in S_0,\\0,&\gamma\notin S_0,\end{cases}\qquad S_0=\operatorname{supp}(\hat f_H),$$
--   and the corrected spectrum $\hat\phi_{a+H}$ is the entire vector occurring most often among the $2^n$ votes at $a$, ties broken by a fixed rule.
--
--   These are the objects of the self-correction argument of §3.2 and of Proposition 3.8.
--
--   **Formalization Note** The most frequent vote is chosen as the vote of a shift maximizing the count of its own vote; the fixed tie rule is Lean's choice function. Nothing about the votes or the corrected spectra is assumed: majority, consistency and realizability are the theorems of the mission.
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 8, Algorithm 1 (steps 3–6); p. 10, §3.2, definition of p_H(f), Eq. (6) and the most frequent vote; PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Basic

set_option autoImplicit false

namespace FourierSparseTesting1656.Uniform

open FourierDimTesting102.Quantum

/-- The restricted spectrum `f̂_{a+H}(γ)`, `γ ∈ W`, of a Boolean `f` (Eq. (2), p.7). -/
noncomputable def rspec {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (f : BoolFn n) (a : V n)
    (γ : W) : ℝ :=
  restrCoeff H W (toSign f) a γ

open Classical in
/-- Algorithm 1, p.8: the checks of `SpectrumTest` for the fixed subspace `H`, the fixed
complement `W` and the shifts `a, r`, on the four restrictions at `0, a, r, a + r`.
1. *Sparsity*: each of the four spectra has at most `s` nonzero coefficients.
2. *Magnitude*: `|f̂_{a+H}(γ)| = |f̂_{r+H}(γ)| = |f̂_{a+r+H}(γ)| = |f̂_H(γ)|` for every `γ ∈ W`.
3. *Triangle*: on `supp(f̂_H)`, the ratio at `a` times the ratio at `r` is the ratio at `a + r`.
4. *Additive*: for `γ₁,γ₂,γ₃,γ₄ ∈ supp(f̂_H)` with `γ₁ + γ₂ = γ₃ + γ₄`, the products of the
   ratios at shift `a` agree.
Ratios `f̂_{t+H}(γ)/f̂_H(γ)` are only formed on `supp(f̂_H)`, where the denominator is nonzero. -/
def checksPass {n : ℕ} (s : ℕ) (H W : Submodule (ZMod 2) (V n)) (f : BoolFn n) (a r : V n) :
    Prop :=
  (∀ t ∈ ({0, a, r, a + r} : Finset (V n)),
      (Finset.univ.filter fun γ : W => rspec H W f t γ ≠ 0).card ≤ s) ∧
  (∀ γ : W, |rspec H W f a γ| = |rspec H W f 0 γ| ∧ |rspec H W f r γ| = |rspec H W f 0 γ| ∧
      |rspec H W f (a + r) γ| = |rspec H W f 0 γ|) ∧
  (∀ γ : W, rspec H W f 0 γ ≠ 0 →
      (rspec H W f a γ / rspec H W f 0 γ) * (rspec H W f r γ / rspec H W f 0 γ) =
        rspec H W f (a + r) γ / rspec H W f 0 γ) ∧
  (∀ γ₁ γ₂ γ₃ γ₄ : W, rspec H W f 0 γ₁ ≠ 0 → rspec H W f 0 γ₂ ≠ 0 → rspec H W f 0 γ₃ ≠ 0 →
      rspec H W f 0 γ₄ ≠ 0 → γ₁ + γ₂ = γ₃ + γ₄ →
      (rspec H W f a γ₁ / rspec H W f 0 γ₁) * (rspec H W f a γ₂ / rspec H W f 0 γ₂) =
        (rspec H W f a γ₃ / rspec H W f 0 γ₃) * (rspec H W f a γ₄ / rspec H W f 0 γ₄))

open Classical in
/-- §3.2, p.10: `p_H(f) = Pr_{a,r}[SpectrumTest rejects | H]`, with `H` (and `W`) fixed and only
the two shifts `a, r` uniform and independent on `F₂ⁿ`. -/
noncomputable def pH {n : ℕ} (s : ℕ) (H W : Submodule (ZMod 2) (V n)) (f : BoolFn n) : ℝ :=
  ((Finset.univ.filter fun ar : V n × V n => ¬ checksPass s H W f ar.1 ar.2).card : ℝ) /
    (2 ^ n * 2 ^ n)

open Classical in
/-- Eq. (6), p.10: the vote of the shift `r` for the whole spectrum on `a + H`,
`f̂_{a+r+H}(γ) f̂_{r+H}(γ) / f̂_H(γ)` on `S₀ = supp(f̂_H)` and `0` off `S₀`. -/
noncomputable def vote {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (f : BoolFn n) (a r : V n) :
    W → ℝ :=
  fun γ => if rspec H W f 0 γ ≠ 0 then
    rspec H W f (a + r) γ * rspec H W f r γ / rspec H W f 0 γ else 0

open Classical in
/-- The number of shifts `r ∈ F₂ⁿ` whose vote at `a` is the vector `v`. -/
noncomputable def voteCount {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (f : BoolFn n) (a : V n)
    (v : W → ℝ) : ℕ :=
  (Finset.univ.filter fun r : V n => vote H W f a r = v).card

/-- A shift whose vote occurs most often among all `2ⁿ` votes at `a`; the fixed tie-breaking
rule is the choice function. -/
noncomputable def winningShift {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (f : BoolFn n)
    (a : V n) : V n :=
  Classical.choose (Finset.exists_max_image (Finset.univ : Finset (V n))
    (fun r => voteCount H W f a (vote H W f a r)) Finset.univ_nonempty)

/-- §3.2, p.10: the corrected spectrum `ϕ̂_{a+H}`, the most frequent entire vote vector at
`a` (over the actual finite multiset of votes), ties broken by a fixed rule. -/
noncomputable def corrected {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (f : BoolFn n)
    (a : V n) : W → ℝ :=
  vote H W f a (winningShift H W f a)

/-- The corrected vector is a vote of maximal frequency. -/
theorem voteCount_le_corrected {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (f : BoolFn n)
    (a r : V n) : voteCount H W f a (vote H W f a r) ≤ voteCount H W f a (corrected H W f a) :=
  (Classical.choose_spec (Finset.exists_max_image (Finset.univ : Finset (V n))
    (fun r => voteCount H W f a (vote H W f a r)) Finset.univ_nonempty)).2 r (Finset.mem_univ r)

end FourierSparseTesting1656.Uniform


