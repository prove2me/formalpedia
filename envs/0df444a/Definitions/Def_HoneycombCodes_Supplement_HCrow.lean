-- Prove2me | Definitions.Def_HoneycombCodes_Supplement_HCrow
-- name    : HoneycombCodes_Supplement_HCrow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:35:22.078177+00:00
-- url     : https://prove2.me/theorems/609fa291-c236-45db-89e1-524b3265d0df
-- title:
--   Certificate libraries $\mathfrak C_r(n)$ and the raw row bound $\mathrm{HC}^{row}_r(n,d)$
-- statement:
--   Let $s_{n,d}=1-2d/n$. A certificate is recorded by its spectral value $\lambda(h)$, $m$, $d_E$, $\Delta(A)$ and kernel $K_h$, with bound $B(h;s)=(1-s)m/(d_E(\lambda(h)-s)\Delta(A))$.
--
--   1. $\mathfrak C_1(n)$ consists exactly of the scalar certificates of Theorem 4.8: for every $0\le k\le n/2$, every connected finite set $\Omega$ of valid triples and every positive profile $w$, the certificate with $\lambda(h)=\lambda_\Omega(w)$, $m=1$, $d_E=d_k$, $\Delta(A)=\sum_\omega(w_\omega/Z)^2/D_\omega$ (so $B(h;s)=(1-s)D_\Omega(w)/(d_k(\lambda_\Omega(w)-s))$), realized as a frame with $F=\mathbb C$, $A_\omega=\sqrt{w_\omega/Z}\,\phi_\omega$ in $B_n$-irreducibles $V_\omega\cong V_{(n-i-j,j),(i-\ell,\ell)}$ with stabilizer type $S^{(n-k,k)}$ (Corollary 7.5).
--   2. For $r\ge2$, $\mathfrak C_r(n)$ contains $\mathfrak C_{r-1}(n)$ and every frame-profile certificate for $G=B_n$, $H=S_n$, $E\cong S^\nu$ with $\nu\vdash n$ of at most $r+1$ rows, supported on a finite box-transfer subgraph of $\Omega_r(\nu)=\{(\lambda,\mu): c^\nu_{\lambda\mu}>0\}$.
--
--   The **raw row bound** is
--
--   $$
--   \mathrm{HC}^{row}_r(n,d)=\inf_{h\in\mathfrak C_r(n),\ \lambda(h)>s_{n,d}}B(h;s_{n,d}),
--   $$
--
--   an empty infimum being $2^n$.
--
--   This is the row axis of the finite honeycomb hierarchy (Theorem 8.1).
--
--   **Formalization Note** Representations live on $\mathbb C^D$ (every finite-dimensional unitary representation is unitarily equivalent to one there). $c^\nu_{\lambda\mu}>0$ is stated as $\mathrm{Hom}_{S_n}(S^\nu,\mathrm{Res}\,V_{\lambda,\mu})\ne0$, which is (95). The recursion for $\mathfrak C_r(n)$ is unwound to $\mathfrak C_1(n)\cup\{$frame certificates for $\nu$ with at most $r+1$ rows$\}$ for $r\ge2$. The scalar data use the published `pDir`, `Domega`, `dk`, `lamProfile`.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §8, eqs. (93)–(97) and the definition of HC^row_r, p.40 (PDF 42); Corollary 7.5, pp.38–39 (PDF 40–41)

import Mathlib
import Definitions.Def_HoneycombCodes_pDir
import Definitions.Def_HoneycombCodes_lamProfile
import Definitions.Def_HoneycombCodes_Supplement_BnTypes
import Definitions.Def_HoneycombCodes_Supplement_FrameCert

set_option autoImplicit false

open scoped InnerProductSpace TensorProduct

namespace HoneycombCodes.Supplement

/-- `ℂ^D` with its standard inner product, the carrier of every representation in the
certificate libraries (every finite-dimensional unitary representation is unitarily equivalent to
one on some `ℂ^D`). -/
abbrev Euc (D : ℕ) : Type := EuclideanSpace ℂ (Fin D)

/-- The distance threshold `s_{n,d} = 1 − 2d/n`, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework
for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), §8, p.40 (PDF 42); `t(x, y) ≤ s_{n,d}`
off the diagonal is minimum distance at least `d` (22). -/
noncomputable def sND (n d : ℕ) : ℝ :=
  1 - 2 * (d : ℝ) / n

/-- The numerical record of a certificate `h` on the cube `{±1}ⁿ` (words `Fin n → Fin 2`): its
spectral value `λ(h)`, `m = dim F`, `d_E`, `Δ(A)` and its kernel `K_h(x, y) = tr(P_x P_y)`
(§§7.2–7.3, pp.37–39, PDF 39–41). -/
structure CertData (n : ℕ) where
  lam : ℝ
  m : ℝ
  dE : ℝ
  Delta : ℝ
  K : (Fin n → Fin 2) → (Fin n → Fin 2) → ℝ

/-- The certificate bound `B(h; s) = (1 − s) m/(d_E (λ − s) Δ(A))` (86), arXiv:2608.20287v2, p.37
(PDF 39). -/
noncomputable def CertData.bound {n : ℕ} (h : CertData n) (s : ℝ) : ℝ :=
  (1 - s) * h.m / (h.dE * (h.lam - s) * h.Delta)

/-- The sign flip `ε_x ∈ C₂ⁿ ⊆ B_n` carrying the base word `o = (1, …, 1)` (bits all `0`) to the word
`x` (bit `1` ↔ sign `−1`); used as the representative `rep x` in `K_h`. -/
def signFlip {n : ℕ} (x : Fin n → Fin 2) : Bn n :=
  SemidirectProduct.inl (fun r => if x r = 0 then 1 else -1)

/-- A **realization** of the scalar profile `w` on the connected two-row truncation `Ω` at
stabilizer type `(n − k, k)` as a frame with `F = ℂ` (Corollary 7.5, pp.38–39, PDF 40–41), and its
kernel `K`: unitary `B_n`-irreducibles `V_ω ≅ V_{(n−i−j, j),(i−ℓ, ℓ)}` for `ω = (i, j, ℓ) ∈ Ω`, a
unitary `S_n`-irreducible `E ≅ S^{(n−k, k)}`, isometric `S_n`-embeddings `ϕ_ω : E → V_ω`, the frame
`A_ω = √(w_ω/Z) ϕ_ω` (`Z = Σ w`), and `K = K_h` computed from it.

**Formalization Note.** `S_n ⊆ B_n` is `inr`; `K_h` does not depend on the choice of the
realization (all choices differ by phases). -/
def IsScalarRealization (n k : ℕ) (Ω : Finset (ℕ × ℕ × ℕ)) (w : Ω → ℝ)
    (K : (Fin n → Fin 2) → (Fin n → Fin 2) → ℝ) : Prop :=
  ∃ (dE : ℕ) (ρE : Representation ℂ (Equiv.Perm (Fin n)) (Euc dE)) (D : Ω → ℕ)
    (ρ : ∀ ω : Ω, Representation ℂ (Bn n) (Euc (D ω)))
    (ϕ : ∀ ω : Ω, Euc dE →ₗ[ℂ] Euc (D ω)),
    IsSpechtType ρE (twoRow (n - k) k) ∧
    (∀ (g : Equiv.Perm (Fin n)) (u u' : Euc dE), ⟪ρE g u, ρE g u'⟫_ℂ = ⟪u, u'⟫_ℂ) ∧
    (∀ ω : Ω, IsBnType (ρ ω) (twoRow (n - ω.1.1 - ω.1.2.1) ω.1.2.1)
      (twoRow (ω.1.1 - ω.1.2.2) ω.1.2.2)) ∧
    (∀ (ω : Ω) (g : Bn n) (v v' : Euc (D ω)), ⟪ρ ω g v, ρ ω g v'⟫_ℂ = ⟪v, v'⟫_ℂ) ∧
    (∀ (ω : Ω) (u : Euc dE), ‖ϕ ω u‖ = ‖u‖) ∧
    (∀ ω : Ω, IsHMap SemidirectProduct.inr ρE (ρ ω) (ϕ ω)) ∧
    K = frameKernel (fun ω => Euc (D ω)) ρ
      (fun ω (b : Fin dE) =>
        ((Real.sqrt (w ω / ∑ ω', w ω') : ℝ) : ℂ) • ϕ ω (EuclideanSpace.single b 1))
      signFlip

/-- The **level-one library** `C₁(n)` (§8, p.40, PDF 42): exactly the scalar certificates of
Theorem 4.8, over every `0 ≤ k ≤ n/2`, every connected finite set `Ω` of valid triples and every
positive profile `w`, with `λ(h) = λ_Ω(w)`, `m = 1`, `d_E = d_k`, `Δ(A) = Σ_ω (w_ω/Z)²/D_ω`, so that
`B(h; s) = (1 − s) D_Ω(w)/(d_k(λ_Ω(w) − s))` (Corollary 7.5), and the kernel of their frame
realization.

**Formalization Note.** `p_{ω,ω′}`, `D_ω`, `d_k`, validity and connectivity are the published
`pDir`, `Domega`, `dk`, `IsValidTriple`, `IsConnectedOmega` (closed forms (32)–(37)); `λ_Ω(w)` is
the published `lamProfile`. -/
def IsC1Cert (n : ℕ) (h : CertData n) : Prop :=
  ∃ (k : ℕ) (Ω : Finset (ℕ × ℕ × ℕ)) (w : Ω → ℝ), 2 * k ≤ n ∧
    (∀ ω ∈ Ω, IsValidTriple n k ω) ∧ IsConnectedOmega n k Ω ∧ (∀ ω, 0 < w ω) ∧
    h.lam = lamProfile (fun a b : Ω => pDir n k a b) w ∧ h.m = 1 ∧ h.dE = dk n k ∧
    h.Delta = ∑ ω : Ω, (w ω / ∑ ω', w ω') ^ 2 / Domega n ω ∧
    IsScalarRealization n k Ω w h.K

/-- A **frame-profile certificate supported on a finite box-transfer subgraph associated with
`ν ∈ Par_r(n)`** (§8, pp.40, PDF 42), recorded as `CertData`: `G = B_n`, `H = S_n` (via `inr`),
`W` the natural signed representation with `ℓ_o = n^{−1/2}(1, …, 1)`, `E ≅ S^ν` with `ν ⊢ n` of at
most `r + 1` rows; a finite family `Ω` of distinct bipartitions `ω = (λ, µ)` in `Ω_r(ν)` (93)–(94),
i.e. with `c^ν_{λµ} = dim Hom_{S_n}(S^ν, Res V_{λ,µ}) > 0` (95), and `V_ω ≅ V_{λ,µ}`; edges only
along box transfers (96); and a frame-profile certificate (Definition 7.3) on these data.

**Formalization Note.** `Ω` is indexed by `Fin N` through the injective labeling `lab`; each
representation lives on some `ℂ^D`; the parallel edges `ω → ν` are `Fin (ne ω ν)`. -/
def IsFrameRowCert (r n : ℕ) (h : CertData n) : Prop :=
  ∃ (ν : ℕ → ℕ) (dE N m : ℕ) (ρE : Representation ℂ (Equiv.Perm (Fin n)) (Euc dE))
    (lab : Fin N → (ℕ → ℕ) × (ℕ → ℕ)) (D : Fin N → ℕ)
    (ρ : ∀ ω, Representation ℂ (Bn n) (Euc (D ω)))
    (ρW : Representation ℂ (Bn n) (Euc n)) (ne : Fin N → Fin N → ℕ)
    (C : ∀ ω ν', Fin (ne ω ν') → (Euc (D ν') →ₗ[ℂ] Euc n ⊗[ℂ] Euc (D ω)))
    (A : ∀ ω, Euc m →ₗ[ℂ] (Euc dE →ₗ[ℂ] Euc (D ω))) (b : ∀ ω ν', Fin (ne ω ν') → ℂ) (lam : ℝ),
    ν (r + 1) = 0 ∧ IsSpechtType ρE ν ∧
    Function.Injective lab ∧ (∀ ω, IsBnType (ρ ω) (lab ω).1 (lab ω).2) ∧
    (∀ ω, ∃ a : Euc dE →ₗ[ℂ] Euc (D ω), a ≠ 0 ∧ IsHMap SemidirectProduct.inr ρE (ρ ω) a) ∧
    (∀ ω ν', 0 < ne ω ν' → IsBoxTransfer (lab ω) (lab ν')) ∧
    IsSignedNatural ρW ∧
    IsFrameSetup SemidirectProduct.inr ρW (ellO n) ρE (fun ω => Euc (D ω)) ρ
      (fun ω ν' => Fin (ne ω ν')) C ∧
    IsFrameCertificate SemidirectProduct.inr (ellO n) ρE (fun ω => Euc (D ω)) ρ
      (fun ω ν' => Fin (ne ω ν')) C (Euc m) A b lam ∧
    h.lam = lam ∧ h.m = m ∧ h.dE = dE ∧ h.Delta = DeltaA (fun ω => Euc (D ω)) (Euc m) A ∧
    h.K = frameKernel (fun ω => Euc (D ω)) ρ (frameVectors (fun ω => Euc (D ω)) (Euc m) A)
      signFlip

/-- The **nested certificate libraries** `C_r(n)` (§8, p.40, PDF 42): `C₁(n)` is the scalar
library; for `r ≥ 2`, `C_r(n) = C_{r−1}(n) ∪ {frame-profile certificates on box-transfer subgraphs
associated with some ν ∈ Par_r(n)}`.

**Formalization Note.** Since `Par_{r′}(n) ⊆ Par_r(n)` for `r′ ≤ r`, unwinding the recursion gives
`C_r(n) = C₁(n) ∪ {frame certificates for ν with at most r + 1 rows}` for `r ≥ 2`, which is the
closed form used here; `r = 0` is not used. -/
def CrLib (r n : ℕ) : Set (CertData n) :=
  {h | IsC1Cert n h ∨ (2 ≤ r ∧ IsFrameRowCert r n h)}

open Classical in
/-- The **raw row bound** `HC^row_r(n, d) = inf {B(h; s_{n,d}) : h ∈ C_r(n), λ(h) > s_{n,d}}`, with an
empty infimum interpreted as `2ⁿ`, arXiv:2608.20287v2, §8, p.40 (PDF 42).

**Formalization Note.** A real `sInf` of the set of certificate values; the set is bounded below by
`A₂(n, d) ≥ 1` (Theorem 7.4), so this is the printed infimum. -/
noncomputable def HCrow (r n d : ℕ) : ℝ :=
  if {B : ℝ | ∃ h ∈ CrLib r n, sND n d < h.lam ∧ B = h.bound (sND n d)} = ∅ then 2 ^ n
  else sInf {B : ℝ | ∃ h ∈ CrLib r n, sND n d < h.lam ∧ B = h.bound (sND n d)}

end HoneycombCodes.Supplement


