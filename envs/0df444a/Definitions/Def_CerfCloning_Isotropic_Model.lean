-- Prove2me | Definitions.Def_CerfCloning_Isotropic_Model
-- name    : CerfCloning_Isotropic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:40.040834+00:00
-- url     : https://prove2.me/theorems/762542ea-9cd4-4cd4-afce-ca5c4c3c26ed
-- title:
--   §I, §III A–C, pp. 2, 12–15 — ME states (3.1), Weyl operators (3.5), Heisenberg channels (3.6), isotropic cloners, double-ME states (3.8), dual amplitudes (3.11), ansatz (3.16)
-- statement:
--   This file fixes the objects of N. J. Cerf's construction of asymmetric Heisenberg cloning machines for an $N$-level quantum system. Throughout, $N \ge 1$ and ket labels are integers modulo $N$, i.e. elements of $\mathbb{Z}_N = \{0, \dots, N-1\}$.
--
--   1. **Maximally entangled states** (Eq. (3.1)). For $m, n \in \mathbb{Z}_N$, the vector of two $N$-level systems
--   $$|\psi_{m,n}\rangle = \frac{1}{\sqrt N}\sum_{j=0}^{N-1} e^{2\pi i\, jn/N}\, |j\rangle\, |j+m\rangle .$$
--   2. **Error operators** (Eq. (3.5)). $U_{m,n} = \sum_{k=0}^{N-1} e^{2\pi i\, kn/N}\, |k+m\rangle\langle k|$; these generalize the Pauli matrices ($m$ is a shift, $n$ a phase).
--   3. **Heisenberg channel** (Eqs. (3.5)–(3.6)). For real weights $p_{m,n}$, the map $\rho \mapsto \sum_{m,n} p_{m,n}\, U_{m,n}\, \rho\, U_{m,n}^\dagger$.
--   4. **Outputs of a cloner.** A $1 \to 2$ cloner is a map $T$ from operators on an $N$-level input $X$ to operators on $A \otimes B$, two $N$-level outputs. Its output maps are $\rho \mapsto \operatorname{Tr}_B T(\rho)$ (output $A$) and $\rho \mapsto \operatorname{Tr}_A T(\rho)$ (output $B$).
--   5. **Isotropic cloner** (p. 2: "cloners whose outputs emerge from (distinct) depolarizing channels"; p. 15). $T$ is an isotropic cloner with depolarizing fractions $\pi_a, \pi_b \in \mathbb{R}$ if $T$ is a quantum channel (completely positive and trace preserving, given by a finite family of Kraus operators $K_i$ with $\sum_i K_i^\dagger K_i = \mathbb 1$) and, for every operator $\rho$,
--   $$\operatorname{Tr}_B T(\rho) = \frac{\pi_a}{N}(\operatorname{Tr}\rho)\,\mathbb 1 + (1-\pi_a)\,\rho, \qquad \operatorname{Tr}_A T(\rho) = \frac{\pi_b}{N}(\operatorname{Tr}\rho)\,\mathbb 1 + (1-\pi_b)\,\rho .$$
--   6. **Double-ME state** (Eq. (3.8)). For amplitudes $\alpha_{m,n} \in \mathbb{C}$, the vector of four $N$-level systems $R, A, B, C$
--   $$|\Psi\rangle_{RA;BC} = \sum_{m,n=0}^{N-1} \alpha_{m,n}\, |\psi_{m,n}\rangle_{RA}\, |\psi_{m,N-n}\rangle_{BC},$$
--   together with the same vector with $A$ and $B$ interchanged, and the reduced (unnormalized) operators $\rho_{RA} = \operatorname{Tr}_{BC}|\Psi\rangle\langle\Psi|$ and $\rho_{RB} = \operatorname{Tr}_{AC}|\Psi\rangle\langle\Psi|$.
--   7. **Dual amplitudes** (Eq. (3.11)). $\beta_{m,n} = \frac1N \sum_{x,y=0}^{N-1} e^{2\pi i (nx-my)/N}\, \alpha_{x,y}$.
--   8. **Isotropic ansatz** (Eq. (3.16)). For $\hat a, a \in \mathbb{C}$, $\alpha_{m,n} = \hat a\, P_{m,n} + a\, F_{m,n}$ with the peaked component $P_{m,n} = \delta_{m,0}\delta_{n,0}$ and the flat component $F_{m,n} = 1/N$.
--
--   These are the objects in terms of which the paper derives the no-cloning inequality $\pi_a + \frac2N\sqrt{\pi_a\pi_b} + \pi_b \ge 1$ for $N$-level systems.
--
--   **Formalization Note** Labels modulo $N$ are elements of `Fin N` with its modular addition; $N - n$ is `-n` in `Fin N`. Exponents use the natural-number products $j\cdot n$, which changes nothing since $e^{2\pi i k/N}$ is $N$-periodic. In two-register objects the reference (or first system) is the first factor of `Fin N × Fin N`; output $A$ is the first factor of the cloner's output. Four-register vectors are functions on $((R,A),(B,C))$, so $\rho_{RA}$ and $\rho_{RB}$ are written as explicit partial sums rather than through a library partial trace. Channels, $\mathrm{id}_R \otimes \Phi$, $|\psi\rangle\langle\psi|$, the partial traces and the depolarizing map $\rho \mapsto \frac{\pi}{N}(\operatorname{Tr}\rho)\mathbb 1 + (1-\pi)\rho$ are the published definitions `QAlgorithms.IsChannel`, `QAlgorithms.idTensorSuperop`, `QAlgorithms.pureDensity`, `WildeQIT.partialTraceRight/Left` and `QAlgorithms.QuditFidelity.depolarizingMap`. The output conditions are required on every matrix, which for a linear map is the same as on every density matrix.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 2 (isotropic cloners), pp. 12–15, Eqs. (3.1), (3.5), (3.6), (3.8), (3.10), (3.11), (3.16)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_WildeQIT_partialTrace

noncomputable section

open scoped Matrix ComplexOrder BigOperators

namespace CerfCloning.Isotropic

open QAlgorithms

/-- The root of unity `e^{2πi k/N}` (Cerf, arXiv:quant-ph/9805024v2, pp. 12–14). -/
def rootOfUnity (N : ℕ) (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ))

/-- Eq. (3.1), p. 12: the maximally entangled state
`|ψ_{m,n}⟩ = N^{-1/2} Σ_j e^{2πi jn/N} |j⟩|j+m⟩` of two `N`-level systems, ket labels taken
modulo `N` (`Fin N` addition). The first factor of `Fin N × Fin N` carries `|j⟩`, the second
`|j+m⟩`. -/
def meState (N : ℕ) (m n : Fin N) : EuclideanSpace ℂ (Fin N × Fin N) :=
  WithLp.toLp 2 (fun p => if p.2 = p.1 + m then rootOfUnity N (p.1.val * n.val) / Real.sqrt N else 0)

/-- Eq. (3.5), p. 13: the error operator `U_{m,n} = Σ_k e^{2πi kn/N} |k+m⟩⟨k|`. -/
def weyl (N : ℕ) (m n : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun i k => if i = k + m then rootOfUnity N (k.val * n.val) else 0

/-- Eqs. (3.5)–(3.6), p. 13: the Heisenberg channel `ρ ↦ Σ_{m,n} p_{m,n} U_{m,n} ρ U_{m,n}†`. -/
def heisenbergChannel (N : ℕ) (p : Fin N → Fin N → ℝ) : Superop (Fin N) (Fin N) :=
  fun ρ => ∑ m, ∑ n, ((p m n : ℝ) : ℂ) • (weyl N m n * ρ * (weyl N m n)ᴴ)

/-- Output `A` of a `1 → 2` cloner `X → A ⊗ B` (the first factor of `Fin N × Fin N` is `A`):
trace out `B`. -/
def outputA {N : ℕ} (T : Superop (Fin N) (Fin N × Fin N)) : Superop (Fin N) (Fin N) :=
  fun ρ => WildeQIT.partialTraceRight (T ρ)

/-- Output `B` of a `1 → 2` cloner `X → A ⊗ B`: trace out `A`. -/
def outputB {N : ℕ} (T : Superop (Fin N) (Fin N × Fin N)) : Superop (Fin N) (Fin N) :=
  fun ρ => WildeQIT.partialTraceLeft (T ρ)

/-- p. 2 and §III C, p. 15: an isotropic cloner with depolarizing fractions `pa`, `pb` is a
quantum channel `X → A ⊗ B` whose two outputs emerge from depolarizing channels with fractions
`pa` and `pb`: `Tr_B T(ρ) = (pa/N) Tr ρ · 𝟙 + (1 − pa) ρ` and likewise for `B`, for every `ρ`. -/
def IsIsotropicCloner (N : ℕ) [NeZero N] (T : Superop (Fin N) (Fin N × Fin N)) (pa pb : ℝ) : Prop :=
  IsChannel T ∧
    (∀ ρ, outputA T ρ = QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) pa ρ) ∧
    (∀ ρ, outputB T ρ = QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) pb ρ)

/-- Eq. (3.8), p. 14: the four-partite vector
`|Ψ⟩_{RA;BC} = Σ_{m,n} α_{m,n} |ψ_{m,n}⟩_{RA} |ψ_{m,N−n}⟩_{BC}`, as a function on
`((R, A), (B, C))`. `-n` in `Fin N` is `N − n` (and `−0 = 0`). -/
def hcmState (N : ℕ) (α : Fin N → Fin N → ℂ) : (Fin N × Fin N) × (Fin N × Fin N) → ℂ :=
  fun x => ∑ m, ∑ n, α m n * meState N m n x.1 * meState N m (-n) x.2

/-- The same vector with `A` and `B` interchanged: registers ordered `((R, B), (A, C))`. -/
def swapAB {N : ℕ} (Ψ : (Fin N × Fin N) × (Fin N × Fin N) → ℂ) :
    (Fin N × Fin N) × (Fin N × Fin N) → ℂ :=
  fun x => Ψ ((x.1.1, x.2.1), (x.1.2, x.2.2))

/-- `ρ_{RA} = Tr_{BC} |Ψ⟩⟨Ψ|` for a vector on `((R, A), (B, C))`. -/
def reducedRA {N : ℕ} (Ψ : (Fin N × Fin N) × (Fin N × Fin N) → ℂ) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  fun x y => ∑ z, Ψ (x, z) * star (Ψ (y, z))

/-- `ρ_{RB} = Tr_{AC} |Ψ⟩⟨Ψ|` for a vector on `((R, A), (B, C))`. -/
def reducedRB {N : ℕ} (Ψ : (Fin N × Fin N) × (Fin N × Fin N) → ℂ) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  reducedRA (swapAB Ψ)

/-- Eq. (3.11), p. 14: the dual amplitudes
`β_{m,n} = N^{-1} Σ_{x,y} e^{2πi(nx − my)/N} α_{x,y}`. -/
def fourierDual (N : ℕ) (α : Fin N → Fin N → ℂ) : Fin N → Fin N → ℂ :=
  fun m n => (1 / (N : ℂ)) * ∑ x, ∑ y,
    Complex.exp (2 * Real.pi * Complex.I *
      (((n.val * x.val : ℕ) : ℂ) - ((m.val * y.val : ℕ) : ℂ)) / (N : ℂ)) * α x y

/-- Eq. (3.16), p. 15: the isotropic amplitudes `α_{m,n} = â P_{m,n} + a F_{m,n}` with the peaked
component `P_{m,n} = δ_{m,0} δ_{n,0}` and the flat component `F_{m,n} = 1/N`. -/
def isoAmplitude (N : ℕ) [NeZero N] (ahat a : ℂ) : Fin N → Fin N → ℂ :=
  fun m n => (if m = 0 ∧ n = 0 then ahat else 0) + a / (N : ℂ)

end CerfCloning.Isotropic


