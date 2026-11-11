-- Prove2me | Definitions.Def_PermDiameter_Binary_LengthGap
-- name    : PermDiameter_Binary_LengthGap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:10:34.101229+00:00
-- url     : https://prove2.me/theorems/6b1994bf-7629-4766-b250-7bb962f2f06a
-- title:
--   Step 1 of the reduction: $G_1=G_0\times C_{q^2}$, $\Sigma_1$, $g_1$, $k_1$ for every admissible choice of $q,m,d_c,c$
-- statement:
--   Section 3 fixes an instance $(\Sigma_0,g_0,k_0)$ of Binary Length: $\Sigma_0\subseteq\mathrm{Sym}(\Omega_0)$ generates $G_0$ of degree $d_0=|\Omega_0|$, $g_0\in G_0$, and $1\in\Sigma_0$ (which does not change any length). Step 1 uses numbers $q,m,d_c$ with $q=4m-3$ and (3.2) $m\ge k_0+10(d_0+d_c)^4+3$, and a permutation $c$ of order $q^2$ on a set $\Omega_c$ of size $d_c$ (Lemma 3.2 computes such data). With $c_1=c$ and $c_3=c^q$:
--   $$G_1=G_0\times C_{q^2}\le\mathrm{Sym}(\Omega_0\uplus\Omega_c),\qquad \Sigma_1=\{(a,c_1):a\in\Sigma_0\}\cup\{(g_0^{-1},c_1^{q})\}\cup\{(1,1)\},$$
--   $$g_1=(1,c_1^{q+k_0}),\qquad k_1=k_0+1,\qquad d_1=d_0+d_c,$$
--   where $(a,b)$ acts on $\Omega_0\uplus\Omega_c$ by $a$ on $\Omega_0$ and $b$ on $\Omega_c$, and $C_{q^2}=\langle c_1\rangle$. $\mathrm{Stab}_{G_1}(\omega)$ is the stabilizer in $G_1$ of a point $\omega\in\Omega_1=\Omega_0\uplus\Omega_c$.
--
--   The structure `LengthGapData` bundles the instance's standing assumptions with every admissible choice of $(q,m,d_c,c)$; the paper's choice (3.1) is one of them. Step 1 creates the length gap of Lemma 3.3.
--
--   **Formalization Note.** $\Omega_0=$ `Fin d0`, $\Omega_c=$ `Fin dc`, $\Omega_1=$ `Fin d0 ⊕ Fin dc`; pairs are `Equiv.Perm.sumCongr`, and $G_1$ is the image of `closure Σ₀ × zpowers c` under `Perm.sumCongrHom`. Lean's `Equiv.Perm` composes right to left (`(g * h) ω = g (h ω)`), while the paper composes left to right; every formula is kept as printed and read in Lean's group. $q=4m-3$ is stated as `q + 3 = 4 * m`.
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 12 (standing instance of §3), p. 13 (§3.1: Lemma 3.2's data, G1, Σ1, g1, k1), p. 11 (direct products of permutation groups)

import Mathlib
import Definitions.Def_PermDiameter_Binary_WordLength

namespace PermDiameter.Binary

/-!
# Step 1 of the reduction: the length gap (Lohrey–Thumm, §3 p. 12 and §3.1, p. 13)

Section 3 fixes an instance `(Σ₀, g₀, k₀)` of Binary Length: `Σ₀ ⊆ Sym(Ω₀)` generates `G₀` of
degree `d₀ = |Ω₀|`, `g₀ ∈ G₀`, and, without loss of generality, `1 ∈ Σ₀` (p. 12). Here
`Ω₀ = Fin d₀`. Step 1 uses numbers `q, m, d_c` and a permutation `c` of order `q²` on a set
`Ω_c` of size `d_c` (Lemma 3.2). The structure below bundles the instance's standing assumptions
together with **every admissible choice** of `q, m, d_c, c`: the properties the section uses
(`q = 4m − 3`, inequality (3.2), `ord(c) = q²`). The paper's choice (3.1) is one of them.

Permutations are Mathlib's `Equiv.Perm`, whose product `g * h` applies `h` first; all
statements of §3 are read in this group (the paper composes left to right). Lengths, diameters,
stabilizers and centrality do not depend on this convention.
-/

open Equiv

/-- The domain `Ω₁ = Ω₀ ⊎ Ω_c` of `G₁ = G₀ × C_{q²}`, of degree `d₁ = d₀ + d_c`. -/
abbrev Omega1 (d0 dc : ℕ) : Type := Fin d0 ⊕ Fin dc

/-- The instance `(Σ₀, g₀, k₀)` of §3 with its standing assumptions (`g₀ ∈ G₀ = ⟨Σ₀⟩`,
`1 ∈ Σ₀`), and an admissible choice of the Step 1 data `q, m, d_c, c`:
`q = 4m − 3` (stated as `q + 3 = 4m`), (3.2) `m ≥ k₀ + 10 (d₀ + d_c)⁴ + 3`, and `c` a
permutation of `Ω_c = Fin d_c` of order `q²`. -/
structure LengthGapData {d0 : ℕ} (Sig0 : Finset (Perm (Fin d0))) (g0 : Perm (Fin d0))
    (k0 : ℕ) where
  /-- `g₀ ∈ G₀ = ⟨Σ₀⟩` (input condition of Binary Length) -/
  hg0 : g0 ∈ Subgroup.closure (Sig0 : Set (Perm (Fin d0)))
  /-- `1 ∈ Σ₀` (p. 12, without loss of generality) -/
  h1 : (1 : Perm (Fin d0)) ∈ Sig0
  /-- the number `q` of (3.1) -/
  q : ℕ
  /-- the number `m` of (3.1) -/
  m : ℕ
  /-- the degree `d_c` of (3.1) -/
  dc : ℕ
  /-- `q = 4m − 3` (proof of Lemma 3.2) -/
  hqm : q + 3 = 4 * m
  /-- inequality (3.2) -/
  h32 : k0 + 10 * (d0 + dc) ^ 4 + 3 ≤ m
  /-- the permutation `c` of Lemma 3.2 on `Ω_c = Fin d_c` -/
  c : Perm (Fin dc)
  /-- `c` has order `q²` -/
  hc : orderOf c = q ^ 2

namespace LengthGapData

variable {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}
variable (D : LengthGapData Sig0 g0 k0)

/-- The degree `d₁ = d₀ + d_c` of `G₁`. -/
def d1 : ℕ := d0 + D.dc

/-- The pair `(a, b) ∈ Sym(Ω₀) × Sym(Ω_c)` acting on `Ω₀ ⊎ Ω_c` (§2.3, p. 11). -/
def pair (a : Perm (Fin d0)) (b : Perm (Fin D.dc)) : Perm (Omega1 d0 D.dc) :=
  Perm.sumCongr a b

/-- `G₁ = G₀ × C_{q²}`, with `C_{q²} = ⟨c₁⟩` and `c₁ = c`, as a permutation group on `Ω₁`. -/
def G1 : Subgroup (Perm (Omega1 d0 D.dc)) :=
  ((Subgroup.closure (Sig0 : Set (Perm (Fin d0)))).prod (Subgroup.zpowers D.c)).map
    (Perm.sumCongrHom (Fin d0) (Fin D.dc))

/-- `Σ₁ = {(a, c₁) : a ∈ Σ₀} ∪ {(g₀⁻¹, c₁^q)} ∪ {(1, 1)}` (p. 13). -/
def Sig1 : Finset (Perm (Omega1 d0 D.dc)) :=
  Sig0.image (fun a => D.pair a D.c) ∪ {D.pair g0⁻¹ (D.c ^ D.q), D.pair 1 1}

/-- The target `g₁ = (1, c₁^{q + k₀})` (p. 13). -/
def g1 : Perm (Omega1 d0 D.dc) := D.pair 1 (D.c ^ (D.q + k0))

/-- `c₃ = c^q`, generating the clock `C_q = ⟨c₃⟩` of order `q` (p. 13). -/
def c3 : Perm (Fin D.dc) := D.c ^ D.q

/-- The threshold `k₁ = k₀ + 1` (p. 13). -/
def k1 (_ : LengthGapData Sig0 g0 k0) : ℕ := k0 + 1

/-- The stabilizer `Stab_{G₁}(ω)` of a point `ω ∈ Ω₁` in `G₁`. -/
def Stab (ω : Omega1 d0 D.dc) : Subgroup (Perm (Omega1 d0 D.dc)) :=
  D.G1 ⊓ MulAction.stabilizer (Perm (Omega1 d0 D.dc)) ω

end LengthGapData

end PermDiameter.Binary


