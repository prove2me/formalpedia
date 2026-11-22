-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_iterH
-- name    : QuantumKtSoI_Supplement_iterH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:25:28.184623+00:00
-- url     : https://prove2.me/theorems/5860d747-c5d5-4bc1-99ff-4af0ca5e0a00
-- title:
--   The iterated logarithms $\Lambda_i$, towers, and the iterated clocks $F^{[j]}_a$, $H^{[j]}_a$ of §5.3
-- statement:
--   For integers $N\ge0$ put $\Lambda_1(N)=\lceil\log(N+4)\rceil$, $\Lambda_2(N)=\lceil\log\Lambda_1(N)\rceil$ and $\Lambda_{i+1}(N)=\lceil\log(\Lambda_i(N)+1)\rceil$ for $i\ge2$. The tower family is $\mathrm{tow}_0(u)=u$, $\mathrm{tow}_j(u)=2^{\mathrm{tow}_{j-1}(u)}$. For integers $j,a\ge1$,
--   $$F^{[j]}_a(N)=\mathrm{tow}_j\big(\Lambda_{j+1}(N)^a\big),\qquad H^{[j]}_a(N)=2^{F^{[j]}_a(N)} .$$
--   For $j=1$ these are the clocks $F_a$ and $H_a$ of §4.5.
--
--   They are the larger error scales of Corollary 5.15, which Theorem D.38 transfers to universal machines.
--
--   **Formalization Note** `LamI i N` is $\Lambda_i(N)$ for $i\ge1$; its unused value at $i=0$ is $N+4$. The tower is taken on natural numbers, since it is only applied to the integers $\Lambda_{j+1}(N)^a$.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), §5.3, p.61

import Mathlib
import Definitions.Def_QuantumKtSoI_Supplement_Ha

namespace QuantumKtSoI.Supplement

/-- The iterated logarithms of §5.3 (p.61): `Λ₁(N) = ⌈log(N+4)⌉`, `Λ₂(N) = ⌈log Λ₁(N)⌉`, and
`Λ_{i+1}(N) = ⌈log(Λ_i(N) + 1)⌉` for `i ≥ 2`.

**Formalization Note** `LamI i N` is `Λ_i(N)` for `i ≥ 1`; the value at `i = 0` is unused and set
to `N + 4`, so that `Λ₁ = ⌈log Λ₀⌉`. -/
def LamI : ℕ → ℕ → ℕ
  | 0, N => N + 4
  | 1, N => Nat.clog 2 (N + 4)
  | 2, N => Nat.clog 2 (Nat.clog 2 (N + 4))
  | i + 3, N => Nat.clog 2 (LamI (i + 2) N + 1)

/-- The tower family `tow₀(u) = u`, `tow_j(u) = 2^{tow_{j−1}(u)}` (p.61), on natural numbers (it
is only applied to the integers `Λ_{j+1}(N)^a`). -/
def tow : ℕ → ℕ → ℕ
  | 0, u => u
  | j + 1, u => 2 ^ tow j u

/-- `F^{[j]}_a(N) = tow_j(Λ_{j+1}(N)^a)` (p.61). -/
def iterF (j a N : ℕ) : ℕ := tow j (LamI (j + 1) N ^ a)

/-- The iterated clock `H^{[j]}_a(N) = 2^{F^{[j]}_a(N)}` (§5.3, p.61), for integers `j, a ≥ 1`. For
`j = 1` these are the clocks `F_a`, `H_a` of §4.5. -/
def iterH (j a N : ℕ) : ℕ := 2 ^ iterF j a N

end QuantumKtSoI.Supplement


