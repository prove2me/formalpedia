-- Prove2me | Definitions.Def_GoodQLTC_faceWalk
-- name    : GoodQLTC_faceWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:43:49.673667+00:00
-- url     : https://prove2.me/theorems/0fc36913-8f86-4d71-a429-c588b93e0054
-- title:
--   Face walk $W_{j\ell}$ and the mixing constant $C_{\mathrm{mix}}$
-- statement:
--   Let $c_{j\ell}=\binom{j}{\ell}2^{j-\ell}$ and $h_I=\sum_{S\supseteq I,\,|S|=j}D_{S\setminus I}$, $D_I=\prod_{i\in I}n_i$. Starting at $f\in X(j)$, choose $v\in X_{\le f}(\ell)$ and $a\in\mathrm{codir}(v)$ uniformly, then $q\in X_{\ge v}\cap X(\mathrm{dir}(v)\cup\{a\})$ uniformly, put $v'=f^{1-\phi_a(v)}_a(q)$, and choose $g\in X_{\ge v'}(j)$ uniformly. $W_{j\ell}(f,g)$ is the transition probability; a path $(v,a,q,v',g)$ has probability $1/(c_{j\ell}(t-\ell)n_ah_{\mathrm{dir}(v)})$ (7.1). The constant $C_{\mathrm{mix}}(t,\tau)$ is the maximum of $\binom tp2^{t-p-1}\tau^q$ over $1\le q<t$, $0\le p\le q$.
--
--   **Formalization Note** $W_{j\ell}(f,g)$ is written as the sum of the path probabilities (7.1); $C_{\mathrm{mix}}$ is the value chosen in the proof of Theorem 7.1 (p.24) and retained in §8.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §7, Equation (7.1), p.23 (PDF p.26); C_mix in the proof of Theorem 7.1, p.24 (PDF p.27)

import Mathlib
import Definitions.Def_GoodQLTC_dir

namespace GoodQLTC

/-- `c_{jℓ} := binom(j, ℓ) 2^{j−ℓ}` (arXiv:2609.20780, §7, p.23). -/
def cConst (j ℓ : ℕ) : ℕ := Nat.choose j ℓ * 2 ^ (j - ℓ)

/-- `h_I := ∑_{S ⊆ [t], I ⊆ S, |S| = j} D_{S∖I}`, `D_I := ∏_{i∈I} n_i` (arXiv:2609.20780, §7,
p.23; §4.1, p.16). -/
def hConst {t : ℕ} (n : Fin t → ℕ) (I : Finset (Fin t)) (j : ℕ) : ℕ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin t) => I ⊆ S ∧ S.card = j), ∏ i ∈ S \ I, n i

open Classical in
/-- The **face walk** `W_{jℓ}` on `X(j)`, Gay–Jeronimo, arXiv:2609.20780 (held version), §7,
p.23: starting at `f`, choose `v ∈ X_{≤f}(ℓ)` and `a ∈ codir(v)` uniformly, then
`q ∈ X_{≥v} ∩ X(dir(v) ∪ {a})` uniformly, put `v' := f_a^{1−ϕ_a(v)}(q)`, and choose
`g ∈ X_{≥v'}(j)` uniformly. `faceWalk φ n j ℓ f g` is the transition probability `W_{jℓ}(f, g)`,
the sum over the paths `(v, a, q, v', g)` of the path probability (7.1)
`1/(c_{jℓ} (t − ℓ) n_a h_{dir(v)})`.

**Formalization Note.** `v'` ranges over the faces of type `dir(v)` below `q` with
`ϕ_a(v') ≠ ϕ_a(v)` (exactly one in a cubical complex). Used for `f, g ∈ X(j)`. -/
noncomputable def faceWalk {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) (n : Fin t → ℕ) (j ℓ : ℕ) (f g : X) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => v ≤ f ∧ fdim φ v = ℓ),
    ∑ a ∈ codir φ v,
      ∑ q ∈ Finset.univ.filter (fun q => dir φ q = insert a (dir φ v) ∧ v ≤ q),
        ∑ v' ∈ Finset.univ.filter (fun v' => dir φ v' = dir φ v ∧ v' ≤ q ∧ φ v' a ≠ φ v a),
          if v' ≤ g then
            1 / ((cConst j ℓ : ℝ) * ((t : ℝ) - ℓ) * (n a : ℝ) * (hConst n (dir φ v) j : ℝ))
          else 0

/-- The mixing constant `C_mix(t, τ)`: the maximum of `binom(t, p) 2^{t−p−1} τ^q` over integers
`1 ≤ q < t` and `0 ≤ p ≤ q`, as chosen in the proof of Theorem 7.1, Gay–Jeronimo,
arXiv:2609.20780 (held version), p.24 (and retained in §8, p.25). **Formalization Note.** A
maximum of positive reals (for `τ ≥ 1`, `t ≥ 2`), computed as a `max`-fold starting from `0`. -/
noncomputable def Cmix (t : ℕ) (τ : ℝ) : ℝ :=
  ((Finset.Ico 1 t ×ˢ Finset.range t).filter fun qp : ℕ × ℕ => qp.2 ≤ qp.1).fold max 0
    fun qp => (Nat.choose t qp.2 : ℝ) * 2 ^ (t - qp.2 - 1) * τ ^ qp.1

end GoodQLTC


