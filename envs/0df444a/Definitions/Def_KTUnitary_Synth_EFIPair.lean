-- Prove2me | Definitions.Def_KTUnitary_Synth_EFIPair
-- name    : KTUnitary_Synth_EFIPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:36:09.938056+00:00
-- url     : https://prove2.me/theorems/35a96d0f-b8b6-4077-bc53-d21a615d6638
-- title:
--   EFI pair relative to a language
-- statement:
--   An **EFI pair relative to a language $L$** consists of two time-uniform families $\{C_{0,n}\}$, $\{C_{1,n}\}$ of valid $L$-oracle quantum circuits (with FPTEAS encodings $f_0,f_1$) whose outputs on security parameter $n$ are mixed states $\rho_{0,n},\rho_{1,n}$ on the same number $m(n)$ of qubits (the output wires are printed with the circuit by the uniformity machine), such that:
--   1. **Statistically far:** for some polynomial $p$ and all sufficiently large $n$,
--   $$\tfrac12\|\rho_{0,n}-\rho_{1,n}\|_1\ \ge\ \frac1{p(n)+1};$$
--   2. **Computationally indistinguishable:** for every non-uniform polynomial-size family $\{D_n\}$ of valid $L$-oracle quantum circuits (any FPTEAS encoding, description length at most $q(n)$ for a polynomial $q$, any choice of input wires and output wire),
--   $$\big|\Pr[D_n(\rho_{0,n})=1]-\Pr[D_n(\rho_{1,n})=1]\big|\ \text{ is negligible}.$$
--
--   EFI pairs are equivalent to quantum commitment schemes and are implied by most computationally secure quantum cryptography [Yan22; BCQ23].
--
--   **Formalization Note** The bound $1/(p(n)+1)$ with $p\in\mathbb N[X]$ ranges over the same bounds as the paper's $1/p(n)$ and avoids $1/0$. Distinguishers need not be uniform (footnote 9). Negligibility is the published `QAdvFew.PoQOracle.Negligible`.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_QCircuit
import Definitions.Def_KTUnitary_Synth_TimeUniform
import Definitions.Def_KTUnitary_Synth_traceDist
import Definitions.Def_KTUnitary_Synth_outputState
import Definitions.Def_KTUnitary_Synth_acceptProb

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **EFI pair relative to a language `L`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38): "An EFI pair is a pair
of time-uniform quantum circuit families `{C_{0,n}}` and `{C_{1,n}}` whose outputs on security
parameter `n` are mixed states `ρ_{0,n}` and `ρ_{1,n}`, respectively, such that the following hold:
1. There exists a polynomial `p` such that, for every sufficiently large `n`,
`½‖ρ_{0,n} − ρ_{1,n}‖₁ ≥ 1/p(n)`. 2. For every polynomial-time quantum circuit family `{D_n}`,
`|Pr[D_n(ρ_{0,n}) = 1] − Pr[D_n(ρ_{1,n}) = 1]| ≤ negl(n)`. For a language `L`, an EFI pair relative to
`L` is defined identically, but with `{C_{0,n}}`, `{C_{1,n}}`, and `{D_n}` all allowed to be `L`-oracle
circuit families." Footnote 9: "The circuit family need not be uniform."

Fields: the FPTEAS encodings `f₀`, `f₁` of the two generator families; the families `C₀`, `C₁` of
valid `L`-oracle circuits; the output size `m n` and output wires; time uniformity in `tup [1^n]`, with
the machine printing the output wires together with the circuit;
`ρ_{b,n} := outputState (C_b n) f_b L (out_b n)`.

* `gap`: for some polynomial `p`, eventually `1/(p(n) + 1) ≤ ½‖ρ_{0,n} − ρ_{1,n}‖₁`.
* `secure`: for every encoding `g` with an FPTEAS, every family `D` of valid `L`-oracle circuits
  whose descriptions have length at most `q(n)` for a polynomial `q`, every choice of input wires
  `inp n` (carrying the `m n` qubits of `ρ_{b,n}`) and of an output wire `o n`, the advantage
  `|Pr[D_n(ρ_{0,n}) = 1] − Pr[D_n(ρ_{1,n}) = 1]|` is negligible.

**Formalization Note** `1/(p(n) + 1)` with `p ∈ ℕ[X]` ranges over the same bounds as the paper's
`1/p(n)` and excludes the degenerate `1/0`. The distinguishers are non-uniform: "polynomial-time"
is a polynomial bound on the description length, and `g`, `D`, `q`, `inp`, `o` are arbitrary. The
generators are uniform, so their output wires (hence `m n`) are computed by the same polynomial-time
machine: wires chosen outside the description would make `ρ_{b,n}` non-uniform, and the entries of
`ρ_{0,n} − ρ_{1,n}` would have no FPSEAS (proof of Theorem 7.14, p. 38). -/
structure EFIPair (L : Oracle) where
  f₀ : Str → ℝ
  f₁ : Str → ℝ
  fpteas₀ : HasFPTEAS f₀
  fpteas₁ : HasFPTEAS f₁
  C₀ : ℕ → QCircuit
  C₁ : ℕ → QCircuit
  valid₀ : ∀ n, (C₀ n).Valid f₀
  valid₁ : ∀ n, (C₁ n).Valid f₁
  m : ℕ → ℕ
  out₀ : (n : ℕ) → Fin (m n) ↪ Fin (C₀ n).N
  out₁ : (n : ℕ) → Fin (m n) ↪ Fin (C₁ n).N
  uniform₀ : TimeUniform (fun n : ℕ => tup [unary n])
    fun n => tup [(C₀ n).code, tup (List.ofFn fun r => Nat.bits (out₀ n r))]
  uniform₁ : TimeUniform (fun n : ℕ => tup [unary n])
    fun n => tup [(C₁ n).code, tup (List.ofFn fun r => Nat.bits (out₁ n r))]
  gap : ∃ p : Polynomial ℕ, ∀ᶠ n : ℕ in Filter.atTop,
    1 / (((p.eval n : ℕ) : ℝ) + 1) ≤
      traceDist (outputState (C₀ n) f₀ L (out₀ n)) (outputState (C₁ n) f₁ L (out₁ n))
  secure : ∀ g : Str → ℝ, HasFPTEAS g → ∀ D : ℕ → QCircuit, (∀ n, (D n).Valid g) →
    ∀ q : Polynomial ℕ, (∀ n, (D n).code.length ≤ q.eval n) →
    ∀ (inp : (n : ℕ) → Fin (m n) ↪ Fin (D n).N) (o : (n : ℕ) → Fin (D n).N),
      Negligible fun n =>
        |acceptProb (D n) g L (inp n) (o n) (outputState (C₀ n) f₀ L (out₀ n)) -
          acceptProb (D n) g L (inp n) (o n) (outputState (C₁ n) f₁ L (out₁ n))|

end KTUnitary.Synth


