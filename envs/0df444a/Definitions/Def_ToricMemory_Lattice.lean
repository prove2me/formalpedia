-- Prove2me | Definitions.Def_ToricMemory_Lattice
-- name    : ToricMemory_Lattice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:44.107138+00:00
-- url     : https://prove2.me/theorems/fb3e4256-4ee9-4ae8-b1e7-c570641d3c1c
-- title:
--   Spacetime lattice of the toric code: sites, links, boundary and the error law
-- statement:
--   The **spacetime lattice** of the toric code with noisy syndrome measurement has the sites $(x,y,t)$ with $x,y\in\mathbb Z_L$ and $t\in\mathbb Z_T$: an $L\times L$ spatial torus repeated over $T$ time slices, with time also periodic. A **link** $(s,d)$ joins the site $s$ to $s+e_d$, where $e_0=(1,0,0)$, $e_1=(0,1,0)$, $e_2=(0,0,1)$. Links in the directions $x$ and $y$ are **horizontal**; an error on one is a qubit flip between two rounds of syndrome measurement. Links in the direction $t$ are **vertical**; an error on one is a faulty syndrome bit. There are $L^2T$ sites, $2L^2T$ horizontal links and $L^2T$ vertical links.
--
--   A **chain** is a set $X$ of links (a $\mathbb Z_2$-chain); the sum of two chains is their symmetric difference. The **boundary** $\partial X$ is the set of sites at which an odd number of link endpoints of $X$ lie, endpoints counted with multiplicity. $H(X)$ and $V(X)$ denote the numbers of horizontal and vertical links of $X$.
--
--   Each link is in error independently, with probability $p$ if horizontal and $q$ if vertical. Writing $p_\ell$ for this probability, the error history is the chain $X$ with probability
--   $$
--   \mu_{p,q}(X)=\prod_{\ell}\begin{cases}p_\ell,&\ell\in X,\\ 1-p_\ell,&\ell\notin X,\end{cases}
--   $$
--   which for $0<p,q<1$ equals $(1-p)^{2L^2T}(1-q)^{L^2T}\big(\tfrac{p}{1-p}\big)^{H}\big(\tfrac{q}{1-q}\big)^{V}$, eq. (44) with its normalization.
--
--   These objects are the setting of every statement of the mission.
--
--   **Formalization Note** Sites are `ZMod L × ZMod L × ZMod T` and links `(site, Fin 3)`; direction `2` is vertical. For $L\le 2$ or $T\le 2$ two links may join the same two sites, and for $L=1$ or $T=1$ a link may be a self-loop (its boundary is empty); the encoding keeps all $3L^2T$ links distinct. Statements assume $L,T\ge1$ (`NeZero`).
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. IV D, pp. 12–13 (error history on horizontal and vertical links, probabilities p and q); Sec. V A, eq. (44), p. 18; link counts Sec. V C, p. 20

import Mathlib

open Finset

namespace ToricMemory

/-- The sites `(x, y, t)` of the spacetime lattice of Dennis–Kitaev–Landahl–Preskill,
*Topological quantum memory*, arXiv:quant-ph/0110143v1, Sec. IV D, p. 13 and Sec. V B–C,
pp. 19–20 (printed page = PDF page): an `L × L` spatial torus repeated over `T` time slices.

**Formalization Note** Time is periodic, so the lattice is the 3-torus
`ZMod L × ZMod L × ZMod T`; this gives exactly the `L²T` sites, `2L²T` horizontal links and
`L²T` vertical links the paper counts on p. 20. `L, T ≥ 1` is imposed by `NeZero` wherever a
finite sum is taken (`ZMod 0 = ℤ`). -/
abbrev Site (L T : ℕ) := ZMod L × ZMod L × ZMod T

/-- A link `(s, d)` of the spacetime lattice joins the site `s` to `s + e_d`
(arXiv:quant-ph/0110143v1, Sec. IV D, p. 13). Directions `0, 1` (spatial `x`, `y`) are
**horizontal** links, which carry qubit errors; direction `2` (time) gives **vertical** links,
which carry syndrome-measurement errors.

**Formalization Note** For `L ≤ 2` or `T ≤ 2` two different links may join the same pair of
sites, and for `L = 1` or `T = 1` a link may be a self-loop; the encoding `(site, direction)` keeps
them distinct, so the counts `2L²T` and `L²T` hold for every `L, T ≥ 1`. -/
abbrev Link (L T : ℕ) := Site L T × Fin 3

/-- The unit vector `e_d` of direction `d`: `e₀ = (1,0,0)`, `e₁ = (0,1,0)`, `e₂ = (0,0,1)`. -/
def dirVec (L T : ℕ) : Fin 3 → Site L T
  | 0 => (1, 0, 0)
  | 1 => (0, 1, 0)
  | 2 => (0, 0, 1)

/-- The initial site `s` of the link `(s, d)`. -/
def src {L T : ℕ} (ℓ : Link L T) : Site L T := ℓ.1

/-- The final site `s + e_d` of the link `(s, d)`. -/
def tgt {L T : ℕ} (ℓ : Link L T) : Site L T := ℓ.1 + dirVec L T ℓ.2

/-- A link is horizontal (spacelike: direction `x` or `y`) when its direction is not `2`. -/
def IsHorizontal {L T : ℕ} (ℓ : Link L T) : Prop := ℓ.2 ≠ 2

instance {L T : ℕ} (ℓ : Link L T) : Decidable (IsHorizontal ℓ) :=
  inferInstanceAs (Decidable (ℓ.2 ≠ 2))

/-- The boundary `∂X` of a chain `X` (a set of links, i.e. a `ℤ₂`-chain;
arXiv:quant-ph/0110143v1, Sec. IV D, p. 12): the sites at which an odd number of link
endpoints of `X` lie. Endpoints are counted with multiplicity, so a self-loop contributes `2` to
its site and has empty boundary. The sum of two chains is their symmetric difference. -/
def boundary {L T : ℕ} [NeZero L] [NeZero T] (X : Finset (Link L T)) : Finset (Site L T) :=
  Finset.univ.filter fun s =>
    (∑ ℓ ∈ X, ((if src ℓ = s then 1 else 0) + (if tgt ℓ = s then 1 else 0) : ℕ)) % 2 = 1

/-- The number `H` of horizontal links of a chain. -/
def hCount {L T : ℕ} (X : Finset (Link L T)) : ℕ := (X.filter IsHorizontal).card

/-- The number `V` of vertical links of a chain. -/
def vCount {L T : ℕ} (X : Finset (Link L T)) : ℕ := (X.filter fun ℓ => ¬ IsHorizontal ℓ).card

/-- The error probability of a link: `p` on a horizontal link (a qubit flip between two
syndrome measurements), `q` on a vertical link (a faulty syndrome bit);
arXiv:quant-ph/0110143v1, Sec. IV D, p. 13. -/
def linkProb {L T : ℕ} (p q : ℝ) (ℓ : Link L T) : ℝ := if IsHorizontal ℓ then p else q

/-- The probability that the error history is exactly the chain `X`, when each link is in error
independently with probability `linkProb p q`:
`μ(X) = ∏_ℓ (p_ℓ if ℓ ∈ X else 1 − p_ℓ)`. For `0 < p, q < 1` this is
`(1−p)^{2L²T}(1−q)^{L²T}·(p/(1−p))^H (q/(1−q))^V`, i.e. eq. (44) of
arXiv:quant-ph/0110143v1, Sec. V A, p. 18, with its normalization.

**Formalization Note** The product form stays meaningful at `p, q ∈ {0, 1}`, where the ratios
of (44) and the logarithms of (46) are undefined. -/
def chainProb {L T : ℕ} [NeZero L] [NeZero T] (p q : ℝ) (X : Finset (Link L T)) : ℝ :=
  ∏ ℓ : Link L T, if ℓ ∈ X then linkProb p q ℓ else 1 - linkProb p q ℓ

end ToricMemory


