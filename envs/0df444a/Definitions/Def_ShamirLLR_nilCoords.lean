-- Prove2me | Definitions.Def_ShamirLLR_nilCoords
-- name    : ShamirLLR_nilCoords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:21.629834+00:00
-- url     : https://prove2.me/theorems/3c341d7b-5580-4d80-ae5e-89ca2776bfd9
-- title:
--   Mal'cev coordinates, first-level characters, vertical frequencies and quadratic orbits
-- statement:
--   Let $G/\Gamma$ be a degree-two filtered nilmanifold with adapted Mal'cev basis $X=(X_1,\dots,X_{d_G})$, $d_2=\dim G_2$, $h=d_G-d_2$. The **Mal'cev coordinate map** $\psi:G\to\mathbb R^{d_G}$ satisfies $\psi(\exp(t_1X_1)\cdots\exp(t_{d_G}X_{d_G}))=t$ and $\psi(\Gamma)=\mathbb Z^{d_G}$; $\psi_1$ is its first $h$ coordinates. A **first-level character** is $\xi(g)=k\cdot\psi_1(g)$ with $k\in\mathbb Z^h$; a **vertical frequency** has real lift $\nu(u)=k_\nu\cdot\psi_2(u)$ on $G_2$, and $\Phi:G/\Gamma\to\mathbb C$ has vertical frequency $\nu$ when
--   $$
--   \Phi(zx)=e(\nu(z))\,\Phi(x)\qquad(z\in G_2,\ x\in G).
--   $$
--   The Lie bracket in basis coordinates is $[v,w]_c=\sum_{a,b}v_aw_bc_{abc}$ with structure constants $[X_a,X_b]=\sum_cc_{abc}X_c$. A **quadratic orbit** is $g(z)=g_0g_1^zg_2^{\binom z2}$ with $g_0,g_1\in G$, $g_2\in G_2$ (this is $\mathrm{poly}(\mathbb Z,G_\bullet)$), and it is $p$-periodic modulo $\Gamma$ when $g(z)^{-1}g(z+p)\in\Gamma$ for all $z$.
--
--   These are the coordinate objects of the product lemma and the local reduction.
--
--   **Formalization Note** The nilmanifold is the published `LSS.Nilmanifold 2`, realized by unipotent matrices; $\psi$ is the inverse of `G.malcev`. Integer rows are stored on all $d_G$ coordinates: a first-level row vanishes on the central coordinates, a central row on the first-level ones.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), §3.1, Eq. (15), p.18; §3.2, Eq. (16)–(17), p.19; §3.4, pp.21–23; §3.5, p.24 (PDF pp.19–25)

import Mathlib
import Definitions.Def_LSSNil

set_option autoImplicit false

namespace ShamirLLR

/-- The additive character `e(t) = exp(2πit)` (§2.3, p.17). -/
noncomputable def eC (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

/-- The Mal'cev coordinate map `ψ : G → ℝ^{d_G}` of the second kind, Eq. (15), p.18:
`ψ(exp(t₁X₁) ⋯ exp(t_{d_G}X_{d_G})) = (t₁, …, t_{d_G})`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
§3.1, Eq. (15), p.18; §3.3, p.20.

**Formalization Note.** A degree-two filtered nilmanifold with an adapted Mal'cev basis is the
published `LSS.Nilmanifold 2`; its element with coordinates `t` is `G.malcev t`. The ordered
exponential map of a Mal'cev basis is a bijection onto `G`, so `ψ` is its inverse
(`Function.invFun`); only its values on `G` are used. Indices are `Fin G.d` (0-based): the first
`h = G.d − G.dimG 2` coordinates are the first-level coordinates `ψ₁` and the last `d₂ = G.dimG 2`
the central coordinates (the last `d₂` basis vectors span `Lie(G₂)`). -/
noncomputable def coord (G : LSS.Nilmanifold 2) (x : G.Mat) : Fin G.d → ℝ :=
  Function.invFun G.malcev x

/-- An integer row `k` on the Mal'cev coordinates is a first-level row: it is supported on the
first `h` coordinates, so `x ↦ k · ψ(x) = k · ψ₁(x)` is a first-level character (§3.4, p.21:
`ξ(g) = k · ψ₁(g)`, `k ∈ ℤ^h`).

**Formalization Note.** A row `k ∈ ℤ^h` is stored as a row on all `d_G` coordinates vanishing on
the central ones. -/
def IsFirstLevel (G : LSS.Nilmanifold 2) (k : Fin G.d → ℤ) : Prop :=
  ∀ j : Fin G.d, G.d - G.dimG 2 ≤ j.val → k j = 0

/-- An integer row supported on the last `d₂` (central) coordinates: the coefficient vector
`k_ν ∈ ℤ^{d₂}` of a vertical frequency `ν(uΓ₂) = k_ν · ψ₂(u)` (§3.4, p.22). -/
def IsCentralRow (G : LSS.Nilmanifold 2) (k : Fin G.d → ℤ) : Prop :=
  ∀ j : Fin G.d, j.val < G.d - G.dimG 2 → k j = 0

/-- The value `k · ψ(x) = ∑_j k_j ψ_j(x)` of an integer row on the Mal'cev coordinates. For a
first-level row this is the first-level character `ξ(x) = k · ψ₁(x)`; for a central row and
`x ∈ G₂` it is the real lift `ν(x) = k_ν · ψ₂(x)` of a vertical frequency (§3.4, pp.21–23). -/
noncomputable def charVal (G : LSS.Nilmanifold 2) (k : Fin G.d → ℤ) (x : G.Mat) : ℝ :=
  ∑ j, (k j : ℝ) * coord G x j

/-- The Lie bracket on `Lie(G)` in basis coordinates: for `v = ∑ v_a X_a`, `w = ∑ w_b X_b`,
`[v, w] = ∑_c (∑_{a,b} v_a w_b c_{abc}) X_c`, with the structure constants
`[X_a, X_b] = ∑_c c_{abc} X_c` (§3.1, p.19). -/
noncomputable def lieBr (G : LSS.Nilmanifold 2) (v w : Fin G.d → ℝ) : Fin G.d → ℝ :=
  fun c => ∑ a, ∑ b, v a * w b * ((G.c a b c : ℚ) : ℝ)

/-- The quadratic orbit in Taylor form `g(z) = g₀ g₁^z g₂^{(z choose 2)}`, Eq. (16), p.19.

**Formalization Note.** Integer powers of the (unipotent, hence invertible) matrices use the
matrix inverse; `(z choose 2) = z(z − 1)/2` is an exact integer. -/
noncomputable def quadOrbit (G : LSS.Nilmanifold 2) (g₀ g₁ g₂ : G.Mat) (z : ℤ) : G.Mat :=
  g₀ * g₁ ^ z * g₂ ^ (z * (z - 1) / 2)

/-- `g ∈ poly(ℤ, G_•)`: a polynomial sequence of degree at most two, which the paper defines as
precisely the Taylor form `g(z) = g₀ g₁^z g₂^{(z choose 2)}` with `g₀, g₁ ∈ G`, `g₂ ∈ G₂`
(Eq. (16), p.19, "We use g ∈ poly(ℤ, G_•) for precisely this form"). -/
def IsQuadPoly (G : LSS.Nilmanifold 2) (g : ℤ → G.Mat) : Prop :=
  ∃ g₀ g₁ g₂ : G.Mat, G.Mem g₀ ∧ G.Mem g₁ ∧ G.MemFil 2 g₂ ∧ g = quadOrbit G g₀ g₁ g₂

/-- `g` is `p`-periodic modulo `Γ`: `g(z + p)Γ = g(z)Γ` for all `z ∈ ℤ`, i.e.
`g(z)⁻¹ g(z + p) ∈ Γ` (Eq. (17), p.19; "periodicity is equivalent to g(z)⁻¹g(z + p) ∈ Γ"). -/
def IsPPeriodic (G : LSS.Nilmanifold 2) (p : ℕ) (g : ℤ → G.Mat) : Prop :=
  ∀ z : ℤ, G.MemΓ ((g z)⁻¹ * g (z + p))

/-- `Φ : G/Γ → ℂ` has vertical frequency `ν` with coefficient row `k_ν` (§3.5, p.24):
`Φ(zx) = e(ν(z)) Φ(x)` for `z ∈ G₂`, `x ∈ G`, where `ν(z) = k_ν · ψ₂(z)` (§3.4, pp.22–23).

**Formalization Note.** Functions on `G/Γ` are right-`Γ`-invariant functions on `G`; the row
`k_ν ∈ ℤ^{d₂}` is stored on all coordinates, vanishing on the first-level ones. -/
def HasVerticalFreq (G : LSS.Nilmanifold 2) (Φ : G.Mat → ℂ) (kν : Fin G.d → ℤ) : Prop :=
  IsCentralRow G kν ∧
    ∀ z x : G.Mat, G.MemFil 2 z → G.Mem x → Φ (z * x) = eC (charVal G kν z) * Φ x

end ShamirLLR


