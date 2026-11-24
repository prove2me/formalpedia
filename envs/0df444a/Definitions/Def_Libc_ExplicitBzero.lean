-- Prove2me | Definitions.Def_Libc_ExplicitBzero
-- name    : Libc_ExplicitBzero
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-24T17:09:54.29607+00:00
-- url     : https://prove2.me/theorems/58c0bbf1-3822-4e90-a0f9-efdbe79882ce
-- title:
--   Contract of explicit_bzero(s, n) and sodium_memzero — zero n bytes at s, in DeepMind's cExtern hook form
-- statement:
--   A contract for C library calls that zero memory, to be used as a hypothesis on a hook (`∀ f, HookOk f Libc.explicitBzeroSpec → …`) by contracts of verified code that calls such a function. It is not from DeepMind: it is written for prove2.me in the form of the hook contracts of the bundle `Musl_ExternHooks`.
--
--   `void explicit_bzero(void *s, size_t n)` first appeared in OpenBSD 5.5 and is provided by glibc, musl and other C libraries; it is not part of POSIX. The OpenBSD manual page ([bzero(3)](https://man.openbsd.org/explicit_bzero.3)) says that `bzero` "writes len zero bytes to the string b" and that the `explicit_bzero()` "variant behaves the same, but will not be removed by a compiler's dead store optimization pass"; the GNU C Library manual ([Erasing Sensitive Data](https://sourceware.org/glibc/manual/latest/html_node/Erasing-Sensitive-Data.html)) describes it the same way. libsodium's `void sodium_memzero(void * const pnt, const size_t len)` has the same signature and effect.
--
--   `explicitBzeroSpec` is `cExtern` applied to: the register condition `x0` $= s$ and `x1` $= n$ (as a natural number); the memory precondition that the callee owns the $n$ bytes from $s$ read-write (`memRegion s n`); and the postcondition that those bytes are all zero (`s ↦ₛ` $n$ zero bytes). So a hook meeting it, entered with `x0` $= s$ and `x1` $= n$, owning those bytes and the 4096 bytes of stack below `sp`, returns to `x30` with `sp` and the callee-saved registers preserved and the $n$ bytes at $s$ set to zero; any assertion about memory it does not own (a frame) still holds afterwards. Nothing is promised about `x0` or the other caller-saved registers on return. The guarantee that the write is not optimized away is about compilation, not about a single call, and is not expressed.
-- source:
--   explicit_bzero: The GNU C Library Reference Manual, "Erasing Sensitive Data", https://sourceware.org/glibc/manual/latest/html_node/Erasing-Sensitive-Data.html, and the OpenBSD manual page bzero(3), https://man.openbsd.org/explicit_bzero.3, contract of explicit_bzero(s, n), in the cExtern form of DeepMind's hook contracts; libsodium's sodium_memzero(pnt, len) has the same signature and effect

module

public import Definitions.Def_Musl_ExternHooks

/-!
# Contract of `explicit_bzero`

A contract for `void explicit_bzero(void *s, size_t n)`, which writes zero to the `n` bytes at `s`
and returns nothing, written in the form of DeepMind's external C hook contracts (`cExtern`, as for
`cryptoMemsetSpec`): `s` in `x0`, `n` in `x1`; the callee owns the `n` bytes at `s` and may use
`externStack` bytes of stack below the caller's stack pointer; afterwards the `n` bytes at `s` are
zero. Nothing is promised about `x0` on return.
-/

@[expose] public section

namespace Libc

open Arm64 ProofLib VerifiedLibraries.Musl

/-- The contract of `explicit_bzero(s, n)`. -/
def explicitBzeroSpec : Spec (BitVec 64 × Nat) :=
  cExtern
    (fun (p, n) s => s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = n)
    (fun (p, n) => memRegion p n)
    (fun (p, n) _ => p ↦ₛ List.replicate n 0#8)

end Libc


